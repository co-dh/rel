#![forbid(unsafe_code)]
//! sort.rs's `dedup` (the numbering of `distinct` and `group`, three engines: bitmap, direct, hashed, and the radix
//! partition), `gather`, and `groupIds`: `number` the groups on one thread, then `fill` each element's id threaded at the lane
//! `ng` fixes.


























// ---- K15: sort.rs's `buckets`, `distinct_fill[_alp]`, `keys_gather_foR` and `parted_of` ----











