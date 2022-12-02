def add(a: BigInt, b:BigInt):BigInt = {
    require(a >= 0)
    require(b >= 0)
    a + b
    0
} ensuring (res => res >= 0 )