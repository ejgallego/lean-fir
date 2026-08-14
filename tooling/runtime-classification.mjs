export function residentHelperFamily(name) {
  if (/^fir_(?:float_(?:box|unbox)|box_|unbox_)/.test(name)) {
    return "resident/boxing";
  }
  if (/^fir_(?:heap_alloc|alloc_|mk_)/.test(name)) {
    return "resident/allocation";
  }
  if (/^fir_(?:inc|dec|release|mark_persistent|isShared)/.test(name)) {
    return "resident/reference-counting";
  }
  if (/Array|array/.test(name)) {
    return "resident/array";
  }
  if (/String|string|utf8/.test(name)) {
    return "resident/string";
  }
  if (/(?:^|[._])(?:Nat|Int)(?:[._]|$)|numeric|big_|uint|sint/.test(name)) {
    return "resident/numeric";
  }
  if (/proj|setter|sproj/.test(name)) {
    return "resident/projection-update";
  }
  return "resident/other";
}
