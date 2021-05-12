// An invalid scenario that is reserved (op: not)
// occurs when there's any bit in the vector (op: wide-or)
// whose TKEEP value is LOW and TSTRB is HIGH (op: not TKEEP and TSTRB)
!(|(~TKEEP & TSTRB));
