import Testing

func nextPowerOfTwo(_ a: Int) -> Int {
    a * 2
}

func greatestCommonDivisor(_ a: Int, _ b: Int) -> Int {
    var a = a
    var b = b

    if a < b {
        swap(&a, &b)
    }

    while b != 0 {
        let r = a % b
        a = b
        b = r
    }
    return a
}

@Test
func gcd(){
    #expect(greatestCommonDivisor(1, 4) == 1)
    #expect(greatestCommonDivisor(4, 1) == 1)
    #expect(greatestCommonDivisor(4, 2) == 2)
    #expect(greatestCommonDivisor(2, 4) == 2)
    #expect(greatestCommonDivisor(12, 8) == 4)
}

func distance(from a: (Int, Int), to b: (Int, Int)) -> Int {
    abs(a.0 - b.0) + abs(a.1 - b.1)
}

func longestCommonPrefix(_ a: [Int], _ b: [Int]) -> [Int] {
    zip(a, b).prefix(while: { $0.0 == $0.1 }).map(\.0)
}

func reverse(_ xs: inout [Int]) {
    for i in 0..<xs.count/2 {
        xs.swapAt(i, xs.count - i - 1)
    }
}

func reversed(_ xs: [Int]) -> [Int] {
    var x = xs
    reverse(&x)
    return x
}

@Test func swa() async throws {
    #expect(reversed([]) == [])
    #expect(reversed([3]) == [3])
    #expect(reversed([3, 4]) == [4, 3])
    #expect(reversed([2, 3, 4]) == [4, 3, 2])
}

func removeWhereEven(_ xs: inout [Int]) {
    xs.removeAll(where: { $0 % 2 == 0 })
}

// func isPalindrome<T: Equatable>(_ s: [T]) -> Bool {
//     // s.lazy.reversed().elementsEqual(s)
//     for i in 0..<s.count {

//     }
// }

// func groupByFirst<T: Hashable, U>(_ xs: [(T, U)]) -> [T: [U]] {}

@preconcurrency import Glibc

func print(s: String) {
    let u = s.utf8CString
    _ = u.withUnsafeBytes{ b in
        fwrite(b.baseAddress, 1, u.count, stdout)
    }
}

@Test func a() {
    print("Hello world!")
}

