# =============================================================================
# File: slr_parser.py
# Description: SLR(1) Parser with GUI — Visual DFA Diagram on Canvas
#              Features: zoom, hover highlight, improved edge routing
# Run: python slr_parser.py   (no external libraries needed)
# =============================================================================

import tkinter as tk
from tkinter import ttk, messagebox, scrolledtext
from collections import defaultdict, OrderedDict
import math

# =============================================================================
# SECTION 1: GRAMMAR
# Parses user input text into productions, terminals, non-terminals.
# Automatically augments with S' -> S.
# =============================================================================

class Grammar:
    def __init__(self):
        self.productions   = []
        self.non_terminals = []
        self.terminals     = set()
        self.start_symbol  = None
        self.aug_start     = None

    def load(self, text):
        """Parse grammar text. Format:  E -> E + T | T  (one rule per line)."""
        self.productions, self.non_terminals, self.terminals = [], [], set()
        seen_nt = OrderedDict()

        for line in [l.strip() for l in text.strip().split('\n') if l.strip()]:
            if '->' not in line:
                raise ValueError(f"Missing '->' in line: '{line}'")
            lhs, rhs_part = line.split('->', 1)
            lhs = lhs.strip()
            if not lhs:
                raise ValueError(f"Empty left-hand side in: '{line}'")
            seen_nt.setdefault(lhs, True)
            for alt in rhs_part.split('|'):
                syms = alt.strip().split()
                if not syms:
                    raise ValueError(f"Empty right-hand side in: '{line}'")
                self.productions.append((lhs, syms))

        self.non_terminals = list(seen_nt.keys())
        self.start_symbol  = self.non_terminals[0]

        nt_set = set(self.non_terminals)
        for _, rhs in self.productions:
            for s in rhs:
                if s not in nt_set and s != 'epsilon':
                    self.terminals.add(s)

        self.aug_start = self.start_symbol + "'"
        while self.aug_start in nt_set:
            self.aug_start += "'"
        self.productions.insert(0, (self.aug_start, [self.start_symbol]))
        self.non_terminals.insert(0, self.aug_start)

    def prod_str(self, i):
        lhs, rhs = self.productions[i]
        return f"{lhs} -> {' '.join(rhs)}"


# =============================================================================
# SECTION 2: FIRST AND FOLLOW SETS
# =============================================================================

class FirstFollow:
    def __init__(self, g: Grammar):
        self.g      = g
        self.first  = defaultdict(set)
        self.follow = defaultdict(set)
        for t in g.terminals:
            self.first[t] = {t}
        self.first['$'] = {'$'}
        self._calc_first()
        self._calc_follow()

    def _calc_first(self):
        changed = True
        while changed:
            changed = False
            for lhs, rhs in self.g.productions:
                before  = len(self.first[lhs])
                eps_all = True
                for sym in rhs:
                    self.first[lhs] |= self.first[sym] - {'epsilon'}
                    if 'epsilon' not in self.first[sym]:
                        eps_all = False
                        break
                if eps_all:
                    self.first[lhs].add('epsilon')
                if len(self.first[lhs]) > before:
                    changed = True

    def first_of_seq(self, syms):
        result, all_eps = set(), True
        for s in syms:
            result |= self.first[s] - {'epsilon'}
            if 'epsilon' not in self.first[s]:
                all_eps = False
                break
        if all_eps:
            result.add('epsilon')
        return result

    def _calc_follow(self):
        self.follow[self.g.aug_start].add('$')
        changed = True
        while changed:
            changed = False
            for lhs, rhs in self.g.productions:
                for i, sym in enumerate(rhs):
                    if sym in self.g.non_terminals:
                        before = len(self.follow[sym])
                        beta   = rhs[i + 1:]
                        fb     = self.first_of_seq(beta) if beta else {'epsilon'}
                        self.follow[sym] |= fb - {'epsilon'}
                        if 'epsilon' in fb:
                            self.follow[sym] |= self.follow[lhs]
                        if len(self.follow[sym]) > before:
                            changed = True


# =============================================================================
# SECTION 3: LR(0) ITEMS AND DFA
# =============================================================================

class Item:
    """Single LR(0) item, e.g.  E -> E • + T"""
    __slots__ = ('pi', 'dp', 'g')

    def __init__(self, prod_index, dot_pos, g: Grammar):
        self.pi, self.dp, self.g = prod_index, dot_pos, g

    @property
    def lhs(self):     return self.g.productions[self.pi][0]
    @property
    def rhs(self):     return self.g.productions[self.pi][1]
    @property
    def dot_sym(self):
        return self.rhs[self.dp] if self.dp < len(self.rhs) else None
    def is_complete(self): return self.dp >= len(self.rhs)
    def advance(self):     return Item(self.pi, self.dp + 1, self.g)
    def __eq__(self, o):   return self.pi == o.pi and self.dp == o.dp
    def __hash__(self):    return hash((self.pi, self.dp))
    def __repr__(self):
        r = list(self.rhs)
        r.insert(self.dp, '•')
        return f"{self.lhs} -> {' '.join(r)}"


class DFA:
    def __init__(self, g: Grammar):
        self.g      = g
        self.states = []
        self.trans  = {}
        self._build()

    def _closure(self, items):
        c = set(items)
        changed = True
        while changed:
            changed = False
            for item in list(c):
                sym = item.dot_sym
                if sym and sym in self.g.non_terminals:
                    for i, (lhs, _) in enumerate(self.g.productions):
                        if lhs == sym:
                            ni = Item(i, 0, self.g)
                            if ni not in c:
                                c.add(ni)
                                changed = True
        return frozenset(c)

    def _goto(self, state, sym):
        moved = {it.advance() for it in state if it.dot_sym == sym}
        return self._closure(moved) if moved else frozenset()

    def _build(self):
        s0 = self._closure({Item(0, 0, self.g)})
        self.states = [s0]
        worklist = [0]
        while worklist:
            idx     = worklist.pop()
            symbols = {it.dot_sym for it in self.states[idx] if it.dot_sym}
            for sym in symbols:
                ns = self._goto(self.states[idx], sym)
                if not ns:
                    continue
                if ns in self.states:
                    ni = self.states.index(ns)
                else:
                    ni = len(self.states)
                    self.states.append(ns)
                    worklist.append(ni)
                self.trans[(idx, sym)] = ni


# =============================================================================
# SECTION 4: SLR PARSING TABLE
# =============================================================================

class SLRTable:
    def __init__(self, g: Grammar, dfa: DFA, ff: FirstFollow):
        self.g, self.dfa, self.ff = g, dfa, ff
        self.action    = {}
        self.goto      = {}
        self.conflicts = []
        self._build()

    def _set_action(self, state, sym, val):
        if (state, sym) in self.action and self.action[(state, sym)] != val:
            self.conflicts.append(
                f"State {state}, '{sym}': "
                f"{self.action[(state, sym)]} vs {val}")
        else:
            self.action[(state, sym)] = val

    def _build(self):
        g, dfa = self.g, self.dfa
        for si, state in enumerate(dfa.states):
            for item in state:
                sym = item.dot_sym
                if sym:
                    if sym in g.terminals and (si, sym) in dfa.trans:
                        self._set_action(si, sym, ('shift', dfa.trans[(si, sym)]))
                    elif sym in g.non_terminals and (si, sym) in dfa.trans:
                        self.goto[(si, sym)] = dfa.trans[(si, sym)]
                else:
                    if item.lhs == g.aug_start:
                        self._set_action(si, '$', ('accept',))
                    else:
                        for t in self.ff.follow[item.lhs]:
                            self._set_action(si, t, ('reduce', item.pi))


# =============================================================================
# SECTION 5: SLR STRING PARSER
# =============================================================================

class SLRParser:
    def __init__(self, g: Grammar, tbl: SLRTable):
        self.g, self.tbl = g, tbl

    def parse(self, text):
        tokens = text.strip().split() + ['$']
        stack  = [0]
        syms   = ['']
        pos    = 0
        steps  = []
        result = 'REJECT'

        for _ in range(500):
            state = stack[-1]
            tok   = tokens[pos]

            stk_display = ' '.join(
                f"{syms[i]} {stack[i]}" for i in range(len(stack))
            ).strip()
            inp_display = ' '.join(tokens[pos:])

            if (state, tok) not in self.tbl.action:
                steps.append({
                    'stack':  stk_display,
                    'input':  inp_display,
                    'action': f'ERROR: no action for state {state}, symbol "{tok}"'
                })
                result = f'REJECT: unexpected symbol "{tok}" in state {state}'
                break

            act = self.tbl.action[(state, tok)]

            if act[0] == 'shift':
                steps.append({
                    'stack':  stk_display,
                    'input':  inp_display,
                    'action': f'Shift  {tok}  -> go to state {act[1]}'
                })
                stack.append(act[1])
                syms.append(tok)
                pos += 1

            elif act[0] == 'reduce':
                lhs, rhs = self.g.productions[act[1]]
                steps.append({
                    'stack':  stk_display,
                    'input':  inp_display,
                    'action': f'Reduce by  {self.g.prod_str(act[1])}'
                })
                for _ in rhs:
                    stack.pop()
                    syms.pop()
                top = stack[-1]
                if (top, lhs) not in self.tbl.goto:
                    result = f'REJECT: no GOTO entry for state {top}, "{lhs}"'
                    break
                stack.append(self.tbl.goto[(top, lhs)])
                syms.append(lhs)

            elif act[0] == 'accept':
                steps.append({
                    'stack':  stk_display,
                    'input':  inp_display,
                    'action': 'ACCEPT'
                })
                result = 'ACCEPT'
                break
        else:
            result = 'REJECT: exceeded step limit (possible loop)'

        return steps, result


# =============================================================================
# SECTION 6: DFA DIAGRAM (Canvas-based visual)
#
# New in this version:
#   - Mouse-wheel ZOOM: scales the entire diagram smoothly
#   - HOVER highlight: mousing over a state brightens its border
#   - Improved edge routing:
#       * Edges between states on the same row are routed with a large
#         vertical arc that clears the box height entirely
#       * Edges between states in different rows/columns use perpendicular
#         offsets that alternate direction per pair index to avoid overlap
#       * Label backgrounds (white-tinted rectangle) keep text readable
# =============================================================================

class DFADiagram:
    # ── Base layout constants (at zoom = 1.0) ────────────────────────
    COLS_PER_ROW = 4
    BOX_W        = 280
    BOX_H        = 150
    H_GAP        = 110
    V_GAP        = 130
    MARGIN       = 80

    # Colour scheme
    CLR_BOX_NORMAL   = '#0a1f3d'
    CLR_BOX_ACCEPT   = '#0a2e1a'
    CLR_BORDER_NORM  = '#4a9eff'
    CLR_BORDER_ACC   = '#4ade80'
    CLR_BORDER_HOVER = '#ffffff'
    CLR_TITLE_TEXT   = '#0d1117'
    CLR_ITEM_TEXT    = '#c7d8f0'
    CLR_MORE_TEXT    = '#64748b'
    CLR_ARROW        = '#f59e0b'
    CLR_LABEL        = '#fde68a'
    CLR_LABEL_BG     = '#1e1e1e'

    def __init__(self, canvas: tk.Canvas):
        self.canvas      = canvas
        self.zoom        = 1.0          # current zoom level
        self.zoom_min    = 0.3
        self.zoom_max    = 3.0
        self._dfa        = None         # stored for redraw on zoom
        self._hovered    = None         # index of currently hovered state
        self._state_bbox = {}           # state_idx -> (x1,y1,x2,y2) in canvas coords

        # Bind zoom to Ctrl+MouseWheel
        canvas.bind('<Control-MouseWheel>', self._on_zoom)
        # Linux scroll events
        canvas.bind('<Control-Button-4>', lambda e: self._zoom_step(1.1, e))
        canvas.bind('<Control-Button-5>', lambda e: self._zoom_step(0.9, e))
        # Hover
        canvas.bind('<Motion>', self._on_motion)
        canvas.bind('<Leave>',  self._on_leave)

    # ── Zoom helpers ─────────────────────────────────────────────────
    def _on_zoom(self, event):
        factor = 1.1 if event.delta > 0 else 0.9
        self._zoom_step(factor, event)

    def _zoom_step(self, factor, event):
        if self._dfa is None:
            return
        new_zoom = max(self.zoom_min, min(self.zoom_max, self.zoom * factor))
        if abs(new_zoom - self.zoom) < 1e-6:
            return
        self.zoom = new_zoom
        self._redraw()

    def _redraw(self):
        if self._dfa is not None:
            self.draw(self._dfa)

    # ── Hover helpers ─────────────────────────────────────────────────
    def _on_motion(self, event):
        # Convert canvas widget coords to canvas scroll coords
        cx = self.canvas.canvasx(event.x)
        cy = self.canvas.canvasy(event.y)
        hit = None
        for idx, (x1, y1, x2, y2) in self._state_bbox.items():
            if x1 <= cx <= x2 and y1 <= cy <= y2:
                hit = idx
                break
        if hit != self._hovered:
            self._hovered = hit
            self._redraw()

    def _on_leave(self, event):
        if self._hovered is not None:
            self._hovered = None
            self._redraw()

    # ── Public draw entry point ───────────────────────────────────────
    def draw(self, dfa: DFA):
        self._dfa = dfa
        c = self.canvas
        c.delete('all')
        self._state_bbox.clear()

        z    = self.zoom
        n    = len(dfa.states)
        cols = self.COLS_PER_ROW
        rows = math.ceil(n / cols)

        bw      = self.BOX_W  * z
        bh      = self.BOX_H  * z
        step_x  = (self.BOX_W + self.H_GAP) * z
        step_y  = (self.BOX_H + self.V_GAP) * z
        margin  = self.MARGIN * z

        total_w = margin * 2 + cols * step_x
        total_h = margin * 2 + rows * step_y
        c.config(scrollregion=(0, 0, total_w, total_h))

        # Compute centre of each state box
        centres = {}
        for i in range(n):
            col = i % cols
            row = i // cols
            cx  = margin + col * step_x + bw / 2
            cy  = margin + row * step_y + bh / 2
            centres[i] = (cx, cy)
            # Store bounding box for hover detection
            self._state_bbox[i] = (cx - bw/2, cy - bh/2,
                                   cx + bw/2, cy + bh/2)

        # Group symbols for each (src, dst) pair
        edge_map = defaultdict(list)
        for (si, sym), di in dfa.trans.items():
            edge_map[(si, di)].append(sym)

        # Assign a curve-side index for parallel edges in the same direction
        pair_counter = defaultdict(int)

        # Draw edges first (under boxes)
        for (si, di), syms in edge_map.items():
            label    = ' | '.join(sorted(syms))
            pair_idx = pair_counter[(min(si, di), max(si, di))]
            pair_counter[(min(si, di), max(si, di))] += 1
            self._draw_edge(centres[si], centres[di], si, di,
                            label, bw, bh, z, pair_idx)

        # Draw state boxes on top
        for i in range(n):
            cx, cy        = centres[i]
            items_sorted  = sorted(repr(it) for it in dfa.states[i])
            is_accept     = any(it.is_complete() for it in dfa.states[i])
            is_hovered    = (i == self._hovered)
            self._draw_box(cx, cy, i, items_sorted, is_accept, is_hovered,
                           bw, bh, z)

    # ── Draw one state box ────────────────────────────────────────────
    def _draw_box(self, cx, cy, idx, items_lines, is_accept,
                  is_hovered, bw, bh, z):
        c  = self.canvas
        hw = bw / 2
        hh = bh / 2
        x1, y1 = cx - hw, cy - hh
        x2, y2 = cx + hw, cy + hh

        fill_clr = self.CLR_BOX_ACCEPT if is_accept else self.CLR_BOX_NORMAL

        if is_hovered:
            border_clr = self.CLR_BORDER_HOVER
            bwidth     = max(2, int(3 * z))
        elif is_accept:
            border_clr = self.CLR_BORDER_ACC
            bwidth     = max(2, int(2 * z))
        else:
            border_clr = self.CLR_BORDER_NORM
            bwidth     = max(2, int(2 * z))

        r = max(4, int(10 * z))
        self._rounded_rect(x1, y1, x2, y2, r, fill_clr, border_clr, bwidth)

        # Title bar
        title_h = max(18, int(24 * z))
        c.create_rectangle(x1 + bwidth, y1 + bwidth,
                           x2 - bwidth, y1 + title_h,
                           fill=border_clr, outline='')

        # State label
        title_font_size = max(7, int(10 * z))
        c.create_text(cx, y1 + title_h / 2 + 1,
                      text=f"I{idx}",
                      fill=self.CLR_TITLE_TEXT,
                      font=('Courier', title_font_size, 'bold'))

        # LR(0) items
        item_font_size = max(5, int(7 * z))
        line_h  = max(10, int(14 * z))
        text_y  = y1 + title_h + max(4, int(6 * z))
        for line in items_lines:
            if text_y + line_h > y2 - 4:
                c.create_text(cx, text_y,
                              text='... (more items)',
                              fill=self.CLR_MORE_TEXT,
                              font=('Courier', item_font_size),
                              anchor='n')
                break
            c.create_text(cx, text_y,
                          text=line,
                          fill=self.CLR_ITEM_TEXT,
                          font=('Courier', item_font_size),
                          anchor='n')
            text_y += line_h

    def _rounded_rect(self, x1, y1, x2, y2, r, fill, outline, width=2):
        c = self.canvas
        c.create_rectangle(x1 + r, y1, x2 - r, y2, fill=fill, outline='')
        c.create_rectangle(x1, y1 + r, x2, y2 - r, fill=fill, outline='')
        for ax, ay, start in [(x1+r, y1+r, 90), (x2-r, y1+r, 0),
                               (x1+r, y2-r, 180), (x2-r, y2-r, 270)]:
            c.create_arc(ax-r, ay-r, ax+r, ay+r,
                         start=start, extent=90, fill=fill, outline='')
        # Border
        c.create_line(x1+r, y1, x2-r, y1, fill=outline, width=width)
        c.create_line(x1+r, y2, x2-r, y2, fill=outline, width=width)
        c.create_line(x1, y1+r, x1, y2-r, fill=outline, width=width)
        c.create_line(x2, y1+r, x2, y2-r, fill=outline, width=width)
        for ax, ay, start in [(x1+r, y1+r, 90), (x2-r, y1+r, 0),
                               (x1+r, y2-r, 180), (x2-r, y2-r, 270)]:
            c.create_arc(ax-r, ay-r, ax+r, ay+r,
                         start=start, extent=90,
                         style='arc', outline=outline, width=width)

    # ── Draw one transition arrow ─────────────────────────────────────
    def _draw_edge(self, p1, p2, si, di, label, bw, bh, z, pair_idx):
        """
        Improved edge routing:
        - Self-loops arc cleanly above the box.
        - Adjacent forward edges (same row, sequential columns) route straight
          with a small upward bow.
        - All other edges are curved with a perpendicular offset that
          alternates direction per pair_idx so parallel edges don't overlap.
        - Edge exits/enters through the box boundary, never through the fill.
        - Labels get a dark background rectangle so they don't blend in.
        """
        c  = self.canvas
        hw = bw / 2
        hh = bh / 2
        x1, y1 = p1
        x2, y2 = p2

        aw = max(2, int(2 * z))   # arrow line width
        font_size = max(6, int(8 * z))

        # ── Self-loop ─────────────────────────────────────────────────
        if si == di:
            top_y  = y1 - hh
            r_loop = max(20, int(30 * z))
            c.create_arc(x1 - r_loop, top_y - r_loop * 1.6,
                         x1 + r_loop, top_y + r_loop * 0.3,
                         start=20, extent=300,
                         style='arc', outline=self.CLR_ARROW, width=aw)
            # Arrowhead tip
            tip_y = top_y + int(r_loop * 0.1)
            ah    = max(4, int(6 * z))
            c.create_polygon(x1 - ah//2, tip_y,
                             x1 + ah//2, tip_y,
                             x1,         tip_y + ah + 2,
                             fill=self.CLR_ARROW, outline='')
            lbl_y = top_y - r_loop * 1.8
            self._draw_label(x1, lbl_y, label, font_size)
            return

        # ── Direction vector ──────────────────────────────────────────
        dx, dy = x2 - x1, y2 - y1
        dist   = math.hypot(dx, dy) or 1
        ux, uy = dx / dist, dy / dist

        # Perpendicular unit vector
        px, py = -uy, ux

        # ── Determine curve offset ────────────────────────────────────
        # Strategy:
        #   * If same row (dy ≈ 0): use a large vertical bow so the
        #     arrow clears the box height entirely.
        #   * Otherwise: curve perpendicular, alternating side per pair_idx
        #     and using a larger offset for backward (si > di) edges.

        same_row = abs(dy) < bh * 0.5

        if same_row:
            # Route over or under the boxes: always go above for forward,
            # below for backward to separate them visually.
            # "Above" means negative y (up on screen).
            if si < di:
                # Forward same-row: arc above the boxes
                curve_dir = -1   # upward
            else:
                # Backward same-row: arc below the boxes
                curve_dir = 1    # downward

            # Bow amount: just enough to clear the box + a margin
            bow = (hh + max(30, int(50 * z))) * curve_dir
            # Mid-point of the straight line, then offset vertically
            mx = (x1 + x2) / 2
            my = (y1 + y2) / 2 + bow

            sx, sy = self._box_edge_pt(x1, y1, hw, hh, ux, uy)
            ex, ey = self._box_edge_pt(x2, y2, hw, hh, -ux, -uy)

        else:
            # General case: perpendicular curve
            # Alternate left/right per pair_idx
            side  = 1 if pair_idx % 2 == 0 else -1
            if si > di:
                # Backward edges get a bigger offset
                curve = max(50, int(80 * z)) * side
            else:
                curve = max(30, int(45 * z)) * side

            # Exit and entry points on box boundaries
            sx, sy = self._box_edge_pt(x1, y1, hw, hh,  ux,  uy)
            ex, ey = self._box_edge_pt(x2, y2, hw, hh, -ux, -uy)

            mx = (sx + ex) / 2 + px * curve
            my = (sy + ey) / 2 + py * curve

        # ── Draw the arrow ────────────────────────────────────────────
        c.create_line(sx, sy, mx, my, ex, ey,
                      smooth=True, arrow=tk.LAST,
                      fill=self.CLR_ARROW, width=aw,
                      arrowshape=(max(8, int(10*z)),
                                  max(10, int(13*z)),
                                  max(3, int(4*z))))

        # ── Label: placed at the quadratic-Bezier midpoint ───────────
        # Bezier at t=0.5: (p0 + 2*p1 + p2) / 4  where p1 = control point
        lx = (sx + 2 * mx + ex) / 4
        ly = (sy + 2 * my + ey) / 4
        # Offset label a little further from the line
        if same_row:
            # Move label away from box top/bottom
            ly_off = -max(10, int(14 * z)) if si < di else max(10, int(14*z))
            self._draw_label(lx, ly + ly_off, label, font_size)
        else:
            # Offset in perpendicular direction
            side  = 1 if pair_idx % 2 == 0 else -1
            loff  = max(10, int(14 * z))
            self._draw_label(lx + px * loff * side,
                             ly + py * loff * side,
                             label, font_size)

    def _draw_label(self, lx, ly, label, font_size):
        """Draw edge label with a dark background for readability."""
        c = self.canvas
        # Draw background first
        pad = max(2, int(3 * self.zoom))
        c.create_rectangle(lx - len(label) * font_size * 0.35 - pad,
                           ly - font_size / 2 - pad,
                           lx + len(label) * font_size * 0.35 + pad,
                           ly + font_size / 2 + pad,
                           fill=self.CLR_LABEL_BG, outline='',
                           stipple='')
        c.create_text(lx, ly, text=label,
                      fill=self.CLR_LABEL,
                      font=('Courier', font_size, 'bold'))

    def _box_edge_pt(self, cx, cy, hw, hh, ux, uy):
        """
        Return the point on the boundary of box (cx,cy,hw,hh)
        in direction (ux,uy), so arrows start/end at the box edge.
        """
        candidates = []
        if abs(ux) > 1e-9:
            t     = hw / abs(ux)
            y_hit = cy + uy * t
            if cy - hh <= y_hit <= cy + hh:
                candidates.append(t)
        if abs(uy) > 1e-9:
            t     = hh / abs(uy)
            x_hit = cx + ux * t
            if cx - hw <= x_hit <= cx + hw:
                candidates.append(t)
        t = min(candidates) if candidates else 0
        return cx + ux * t, cy + uy * t


# =============================================================================
# SECTION 7: GUI (Tkinter)
# =============================================================================

class App:
    def __init__(self, root):
        self.root   = root
        root.title("SLR(1) Parser — Compiler Construction Project")
        root.geometry("1200x820")
        root.configure(bg="#1a1a2e")

        self.grammar = None
        self.ff      = None
        self.dfa     = None
        self.tbl     = None
        self.parser  = None

        self._build_ui()

    # ──────────────────────────────────────────────────────────────────
    # UI Construction
    # ──────────────────────────────────────────────────────────────────
    def _build_ui(self):
        top = tk.LabelFrame(
            self.root, text=" Grammar Input ",
            bg="#0f172a", fg="#94a3b8",
            font=("Courier", 9), bd=1, relief='groove')
        top.pack(fill=tk.X, padx=10, pady=6)

        tk.Label(top,
                 text="  Enter grammar below (one rule per line).   "
                      "Example:   E -> E + T | T",
                 bg="#0f172a", fg="#64748b",
                 font=("Courier", 8)).pack(anchor='w', pady=(4, 0))

        self.gram_in = scrolledtext.ScrolledText(
            top, height=4, font=("Courier", 10),
            bg="#0d1117", fg="#4ade80",
            insertbackground="white", relief='flat')
        self.gram_in.pack(fill=tk.X, padx=6, pady=4)
        self.gram_in.insert(tk.END,
                            "E -> E + T | T\n"
                            "T -> T * F | F\n"
                            "F -> ( E ) | id")

        btn_row = tk.Frame(top, bg="#0f172a")
        btn_row.pack(anchor='w', padx=6, pady=(0, 6))
        tk.Button(btn_row, text="  Generate Parser  ",
                  command=self._generate,
                  bg="#2563eb", fg="white",
                  font=("Courier", 10, "bold"),
                  padx=6, pady=4, relief='flat',
                  cursor='hand2').pack(side=tk.LEFT, padx=(0, 10))
        tk.Button(btn_row, text="  Clear All  ",
                  command=self._clear,
                  bg="#374151", fg="white",
                  font=("Courier", 9),
                  padx=6, pady=4, relief='flat',
                  cursor='hand2').pack(side=tk.LEFT)

        sty = ttk.Style()
        sty.theme_use('default')
        sty.configure('TNotebook', background='#1a1a2e', borderwidth=0)
        sty.configure('TNotebook.Tab',
                      background='#0f172a', foreground='#94a3b8',
                      font=('Courier', 9, 'bold'), padding=[14, 5])
        sty.map('TNotebook.Tab',
                background=[('selected', '#1e3a5f')],
                foreground=[('selected', '#4a9eff')])

        self.nb = ttk.Notebook(self.root)
        self.nb.pack(fill=tk.BOTH, expand=True, padx=10, pady=(0, 8))

        self.tab_ff = tk.Frame(self.nb, bg="#0d1117")
        self.nb.add(self.tab_ff, text="  FIRST / FOLLOW  ")
        self.ff_text = self._make_stext(self.tab_ff)

        self.tab_dfa = tk.Frame(self.nb, bg="#0d1117")
        self.nb.add(self.tab_dfa, text="  DFA Diagram  ")
        self._build_dfa_tab()

        self.tab_tbl = tk.Frame(self.nb, bg="#0d1117")
        self.nb.add(self.tab_tbl, text="  Parsing Table  ")
        self.tbl_container = tk.Frame(self.tab_tbl, bg="#0d1117")
        self.tbl_container.pack(fill=tk.BOTH, expand=True)

        self.tab_parse = tk.Frame(self.nb, bg="#0d1117")
        self.nb.add(self.tab_parse, text="  Parse String  ")
        self._build_parse_tab()

    def _build_dfa_tab(self):
        info = tk.Label(
            self.tab_dfa,
            text="  Blue border = normal state    "
                 "Green border = reduce/accept state    "
                 "White border = hovered    "
                 "Ctrl+Scroll = Zoom In/Out    "
                 "Scroll = Pan",
            bg="#0d1117", fg="#64748b",
            font=("Courier", 8), anchor='w')
        info.pack(fill=tk.X, pady=3)

        frm = tk.Frame(self.tab_dfa, bg="#0d1117")
        frm.pack(fill=tk.BOTH, expand=True)

        hbar = tk.Scrollbar(frm, orient=tk.HORIZONTAL)
        vbar = tk.Scrollbar(frm, orient=tk.VERTICAL)
        self.dfa_canvas = tk.Canvas(
            frm, bg="#0d1117",
            xscrollcommand=hbar.set, yscrollcommand=vbar.set,
            highlightthickness=0)
        hbar.config(command=self.dfa_canvas.xview)
        vbar.config(command=self.dfa_canvas.yview)

        self.dfa_canvas.grid(row=0, column=0, sticky='nsew')
        vbar.grid(row=0, column=1, sticky='ns')
        hbar.grid(row=1, column=0, sticky='ew')
        frm.rowconfigure(0, weight=1)
        frm.columnconfigure(0, weight=1)

        # Scroll with mouse wheel (pan)
        self.dfa_canvas.bind(
            '<MouseWheel>',
            lambda e: self.dfa_canvas.yview_scroll(
                -1 * (e.delta // 120), 'units'))
        self.dfa_canvas.bind(
            '<Shift-MouseWheel>',
            lambda e: self.dfa_canvas.xview_scroll(
                -1 * (e.delta // 120), 'units'))
        # Linux pan
        self.dfa_canvas.bind(
            '<Button-4>',
            lambda e: self.dfa_canvas.yview_scroll(-1, 'units'))
        self.dfa_canvas.bind(
            '<Button-5>',
            lambda e: self.dfa_canvas.yview_scroll(1, 'units'))

        self.diagram = DFADiagram(self.dfa_canvas)

    def _build_parse_tab(self):
        ctrl = tk.Frame(self.tab_parse, bg="#0d1117")
        ctrl.pack(fill=tk.X, padx=8, pady=6)

        tk.Label(ctrl,
                 text="Input String (space-separated tokens): ",
                 bg="#0d1117", fg="#94a3b8",
                 font=("Courier", 9)).pack(side=tk.LEFT)

        self.str_in = tk.Entry(ctrl, font=("Courier", 10), width=34,
                               bg="#1e293b", fg="#4ade80",
                               insertbackground="white", relief='flat')
        self.str_in.pack(side=tk.LEFT, padx=8)
        self.str_in.insert(0, "id + id * id")

        tk.Button(ctrl, text="  Parse String  ",
                  command=self._do_parse,
                  bg="#16a34a", fg="white",
                  font=("Courier", 10, "bold"),
                  padx=6, pady=3, relief='flat',
                  cursor='hand2').pack(side=tk.LEFT)

        self.result_lbl = tk.Label(
            self.tab_parse, text="",
            font=("Courier", 13, "bold"), bg="#0d1117")
        self.result_lbl.pack(pady=2)

        cols = ("Step", "Stack", "Input", "Action")
        frm  = tk.Frame(self.tab_parse, bg="#0d1117")
        frm.pack(fill=tk.BOTH, expand=True, padx=8, pady=4)

        xs = tk.Scrollbar(frm, orient=tk.HORIZONTAL)
        ys = tk.Scrollbar(frm, orient=tk.VERTICAL)

        sty = ttk.Style()
        sty.configure('Parse.Treeview',
                      background='#0f172a', foreground='#e2e8f0',
                      fieldbackground='#0f172a',
                      font=('Courier', 9), rowheight=20)
        sty.configure('Parse.Treeview.Heading',
                      background='#1e3a5f', foreground='#4a9eff',
                      font=('Courier', 9, 'bold'))

        self.parse_tree = ttk.Treeview(
            frm, columns=cols, show='headings',
            style='Parse.Treeview',
            xscrollcommand=xs.set, yscrollcommand=ys.set)
        xs.config(command=self.parse_tree.xview)
        ys.config(command=self.parse_tree.yview)

        widths = {"Step": 55, "Stack": 270, "Input": 200, "Action": 330}
        for col in cols:
            self.parse_tree.heading(col, text=col)
            self.parse_tree.column(col, width=widths[col],
                                   anchor='w', minwidth=50)

        self.parse_tree.grid(row=0, column=0, sticky='nsew')
        ys.grid(row=0, column=1, sticky='ns')
        xs.grid(row=1, column=0, sticky='ew')
        frm.rowconfigure(0, weight=1)
        frm.columnconfigure(0, weight=1)

    def _make_stext(self, parent):
        st = scrolledtext.ScrolledText(
            parent, font=("Courier", 10),
            wrap=tk.NONE, state=tk.DISABLED,
            bg="#0d1117", fg="#a5f3fc",
            insertbackground="white")
        st.pack(fill=tk.BOTH, expand=True, padx=4, pady=4)
        return st

    # ──────────────────────────────────────────────────────────────────
    # Button Handlers
    # ──────────────────────────────────────────────────────────────────
    def _generate(self):
        text = self.gram_in.get("1.0", tk.END).strip()
        if not text:
            messagebox.showerror("Error", "Please enter a grammar first.")
            return

        self.grammar = self.ff = self.dfa = self.tbl = self.parser = None

        try:
            self.grammar = Grammar()
            self.grammar.load(text)

            self.ff  = FirstFollow(self.grammar)
            self.dfa = DFA(self.grammar)
            self.tbl = SLRTable(self.grammar, self.dfa, self.ff)

            self.parser = SLRParser(self.grammar, self.tbl)

            self._display_ff()
            self._display_dfa()
            self._display_table()

            if self.tbl.conflicts:
                messagebox.showwarning(
                    "SLR Conflicts Detected",
                    "This grammar has SLR(1) conflicts "
                    "(not a valid SLR(1) grammar):\n\n" +
                    "\n".join(self.tbl.conflicts))
            else:
                messagebox.showinfo(
                    "Success",
                    f"Parser generated successfully!\n"
                    f"  States      : {len(self.dfa.states)}\n"
                    f"  Productions : {len(self.grammar.productions)}\n"
                    f"  Terminals   : "
                    f"{', '.join(sorted(self.grammar.terminals))}")

        except Exception as exc:
            self.grammar = self.ff = self.dfa = self.tbl = self.parser = None
            messagebox.showerror("Error", str(exc))

    def _display_ff(self):
        lines = ["FIRST Sets", "=" * 50]
        for nt in self.grammar.non_terminals:
            s = ', '.join(sorted(self.ff.first[nt]))
            lines.append(f"  FIRST( {nt} )  =  {{ {s} }}")
        lines += ["", "FOLLOW Sets", "=" * 50]
        for nt in self.grammar.non_terminals:
            s = ', '.join(sorted(self.ff.follow[nt]))
            lines.append(f"  FOLLOW( {nt} )  =  {{ {s} }}")
        self._write(self.ff_text, '\n'.join(lines))

    def _display_dfa(self):
        self.diagram.draw(self.dfa)

    def _display_table(self):
        for w in self.tbl_container.winfo_children():
            w.destroy()

        g     = self.grammar
        terms = sorted(g.terminals) + ['$']
        nts   = [nt for nt in g.non_terminals if nt != g.aug_start]
        cols  = ['State'] + terms + nts

        hdr = tk.Frame(self.tbl_container, bg="#0d1117")
        hdr.pack(fill=tk.X, padx=6, pady=(6, 0))
        tk.Label(hdr, text="  ACTION  ",
                 bg="#2563eb", fg="white",
                 font=("Courier", 9, "bold"),
                 width=max(1, len(terms) * 8)
                 ).pack(side=tk.LEFT, padx=2)
        tk.Label(hdr, text="  GOTO  ",
                 bg="#16a34a", fg="white",
                 font=("Courier", 9, "bold"),
                 width=max(1, len(nts) * 8)
                 ).pack(side=tk.LEFT, padx=2)

        sty = ttk.Style()
        sty.configure('Tbl.Treeview',
                      background='#0f172a', foreground='#e2e8f0',
                      fieldbackground='#0f172a',
                      font=('Courier', 9), rowheight=20)
        sty.configure('Tbl.Treeview.Heading',
                      background='#1e3a5f', foreground='#f59e0b',
                      font=('Courier', 9, 'bold'))

        xs = tk.Scrollbar(self.tbl_container, orient=tk.HORIZONTAL)
        ys = tk.Scrollbar(self.tbl_container, orient=tk.VERTICAL)
        tv = ttk.Treeview(self.tbl_container, columns=cols,
                          show='headings', style='Tbl.Treeview',
                          xscrollcommand=xs.set, yscrollcommand=ys.set)
        xs.config(command=tv.xview)
        ys.config(command=tv.yview)

        for col in cols:
            tv.heading(col, text=col)
            tv.column(col, width=78, anchor='center', minwidth=55)

        for s in range(len(self.dfa.states)):
            row = [str(s)]
            for t in terms:
                a = self.tbl.action.get((s, t))
                if   a is None:         row.append('')
                elif a[0] == 'shift':   row.append(f's{a[1]}')
                elif a[0] == 'reduce':  row.append(f'r{a[1]}')
                else:                   row.append('acc')
            for nt in nts:
                row.append(str(self.tbl.goto[(s, nt)])
                           if (s, nt) in self.tbl.goto else '')
            tv.insert('', tk.END, values=row)

        tv.pack(fill=tk.BOTH, expand=True, padx=6)
        xs.pack(fill=tk.X, padx=6)

    def _do_parse(self):
        if not self.parser:
            messagebox.showerror("Error", "Please generate the parser first.")
            return
        s = self.str_in.get().strip()
        if not s:
            messagebox.showerror("Error", "Please enter an input string.")
            return
        try:
            steps, result = self.parser.parse(s)

            for row in self.parse_tree.get_children():
                self.parse_tree.delete(row)
            for i, step in enumerate(steps):
                self.parse_tree.insert('', tk.END, values=(
                    i + 1,
                    step['stack'],
                    step['input'],
                    step['action']))

            accepted = (result == 'ACCEPT')
            self.result_lbl.config(
                text=f"  {'ACCEPT' if accepted else result}",
                fg="#4ade80" if accepted else "#f87171")

            self.nb.select(self.tab_parse)
        except Exception as exc:
            messagebox.showerror("Parsing Error", str(exc))

    def _clear(self):
        self.gram_in.delete("1.0", tk.END)
        self.gram_in.insert(tk.END,
                            "E -> E + T | T\n"
                            "T -> T * F | F\n"
                            "F -> ( E ) | id")
        self._write(self.ff_text, "")
        self.dfa_canvas.delete('all')
        for w in self.tbl_container.winfo_children():
            w.destroy()
        for row in self.parse_tree.get_children():
            self.parse_tree.delete(row)
        self.result_lbl.config(text="")
        self.grammar = self.ff = self.dfa = self.tbl = self.parser = None

    @staticmethod
    def _write(widget, text):
        widget.config(state=tk.NORMAL)
        widget.delete("1.0", tk.END)
        widget.insert(tk.END, text)
        widget.config(state=tk.DISABLED)


# =============================================================================
# ENTRY POINT
# =============================================================================

if __name__ == "__main__":
    root = tk.Tk()
    App(root)
    root.mainloop()