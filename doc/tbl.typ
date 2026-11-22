// shared by the design notes: striped table with a coloured header, column widths by max-min fair allocation
#let soft(c) = c.lighten(88%)

// `auto` and `fr` columns are sized by content, as HTML tables do: need = widest unwrapped cell + inset.
// If all needs fit, each gets its need plus a share of the slack in proportion to it; otherwise water-fill:
// a column needing less than the equal share keeps its need, the rest split what is left equally.
// Explicit lengths (pt, cm, %) are kept as given. Why: a per-column cap lets long `auto` cells starve the rest.
#let col-widths(cols, needs, total) = {
  let by-content(c) = c == auto or type(c) == fraction
  let resolve(c) = if type(c) == ratio { c * total } else if type(c) == relative { c.length + c.ratio * total } else { c }
  let left = total - cols.filter(c => not by-content(c)).map(resolve).fold(0pt, (a, b) => a + b)
  let idx = range(cols.len()).filter(i => by-content(cols.at(i)))
  let w = (:)
  let pool = idx
  let sum(ids) = ids.map(i => needs.at(i)).fold(0pt, (a, b) => a + b)
  if sum(idx) <= left {
    for i in idx { w.insert(str(i), needs.at(i) * (left / sum(idx))) }
  } else {
    let go = true
    while go and pool.len() > 0 {
      let share = left / pool.len()
      let small = pool.filter(i => needs.at(i) <= share)
      go = small.len() > 0
      for i in small { w.insert(str(i), needs.at(i)); left -= needs.at(i) }
      pool = pool.filter(i => i not in small)
    }
    for i in pool { w.insert(str(i), left / pool.len()) }
  }
  cols.enumerate().map(((i, c)) => if by-content(c) { w.at(str(i)) } else { c })
}

#let tbl(color, cols, head, ..cells) = layout(size => {
  let needs = range(cols.len()).map(i => calc.max(..(head.at(i), ..cells.pos().enumerate()
    .filter(((k, _)) => calc.rem(k, cols.len()) == i).map(((_, x)) => x)).map(x => measure(x).width)) + 12pt)
  table(
    columns: col-widths(cols, needs, size.width),
    stroke: none, inset: (x: 6pt, y: 4.5pt),
    fill: (_, y) => if y == 0 { color } else if calc.even(y) { soft(color) } else { white },
    table.header(..head.map(h => text(fill: white, weight: "bold", font: "Noto Sans CJK SC", h))),
    ..cells, table.hline(stroke: 0.8pt + color))
})
