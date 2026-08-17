import FrontEnd
import Utilities

/// The memory of an interpreted process.
struct Memory {

  /// The program being interpreted.
  public var program: Program

  /// The type layouts computed so far.
  internal var typeLayouts: TypeLayoutCache

  /// The ID of the next block to be allocated.
  private var nextAllocation = 0

  /// The live allocations, by ID
  private var allocation: [Allocation.ID: Allocation] = [:]

  /// Creates an instance to run `p` on `platform`.
  public init(forRunning p: Program, on platform: any TargetABI) {
    program = p
    typeLayouts = .init(for: platform)
  }

  /// An incorrect use of memory.
  public enum Error: Swift.Error, Regular {
    case alignment(Address, for: TypeLayout)
    case bounds(Address, for: TypeLayout, allocationSize: Int)
    case deallocationNotAtStartOfAllocation(Address)
    case noLongerAllocated(Address)
  }

  /// A position in some allocation.
  public typealias Offset = Int

  /// The bytes of an `Allocation` preceded by zero or more bytes of initial padding for alignment
  /// purposes.
  public typealias Storage = [UInt8]

  /// A usable region.
  public struct Allocation {

    /// A unique `Allocation` identifier.
    public typealias ID = Int

    /// The bytes preceded by zero or more bytes of initial padding for alignment purposes.
    var storage: Storage

    /// The number of bytes in `storage` before `self` logically begins.
    public let baseOffset: Offset

    /// The number of usable bytes of `self`.
    public let size: Int

    /// The identity of `self`, unique throughout time for a given `Memory`.
    public let id: ID

    /// A region within an `Allocation`, identified by a starting offset
    /// and the type layout associated with that location.
    public struct TypedRegion: Regular {

      /// Where the region begins relative to an `Allocation`'s `baseOffset`.
      let offset: Offset

      /// The type in the region.
      let type: MonomorphicTypeIdentity

    }

    /// Creates an instance having `n` bytes with alignment `m` and the given `id`.
    private init(_ n: Int, bytesWithAlignment m: Int, id: ID) {
      precondition(n >= 0)
      precondition(m > 0)

      let (s, o) = Storage.aligned(repeating: 0, count: n, alignment: m)
      storage = s
      baseOffset = o
      size = n
      self.id = id
    }

    /// An allocation for `n` contiguous `t`s with the given `id`.
    public init(_ t: TypeLayout, count n: Int, id: ID) {
      self.init(t.size * n, bytesWithAlignment: t.alignment, id: id)
    }

    /// The address of the `o`th byte.
    private func address(at o: Offset) -> Address { .init(allocation: id, offset: o) }

    /// Throws iff there is not enough allocated space for a `t` at `a`, or if it would not be
    /// properly aligned.
    internal func checkAlignmentAndAllocationBounds(at a: Offset, for t: TypeLayout) throws {
      guard offset(a, hasAlignment: t.alignment) else {
        throw Error.alignment(address(at: a), for: t)
      }
      guard a + t.size <= self.size else {
        throw Error.bounds(address(at: a), for: t, allocationSize: self.size)
      }
    }

    /// Returns the result of calling `body` on the storage for a `T` instance at `a`.
    ///
    /// - Precondition: the storage exists and is properly aligned.
    internal mutating func withUnsafeMutablePointer<T, R>(
      to _: T.Type, at a: Offset, _ body: (UnsafeMutablePointer<T>) -> R
    ) -> R {
      precondition(a + MemoryLayout<T>.size <= size)
      precondition(offset(a, hasAlignment: MemoryLayout<T>.alignment))
      return storage.withUnsafeMutableBytes { p in
        body((p.baseAddress! + baseOffset + a).assumingMemoryBound(to: T.self))
      }
    }

    /// Returns the result of calling `body` on the storage for a `T` instance at `a`.
    ///
    /// - Precondition: the storage exists and is properly aligned.
    internal func withUnsafePointer<T, R>(
      to _: T.Type, at a: Offset, _ body: (UnsafePointer<T>) -> R
    ) -> R {
      precondition(a + MemoryLayout<T>.size <= size)
      return storage.withUnsafeBytes { p in
        body((p.baseAddress! + baseOffset + a).assumingMemoryBound(to: T.self))
      }
    }

    /// Returns the unsigned interpretation of `t` at `a`.
    internal func unsignedIntValue(at a: Offset, ofType t: MachineType) -> UInt {
      if case .i(let n) = t {
        return switch n {
        case 8: UInt(withUnsafePointer(to: UInt8.self, at: a) { $0.pointee })
        case 16: UInt(withUnsafePointer(to: UInt16.self, at: a) { $0.pointee })
        case 32: UInt(withUnsafePointer(to: UInt32.self, at: a) { $0.pointee })
        case 64: UInt(withUnsafePointer(to: UInt64.self, at: a) { $0.pointee })
        default: fatalError("Unknown builtin integer size \(n)")
        }
      } else {
        preconditionFailure("Unrecognized builtin integer type \(t)")
      }
    }

    /// Returns `true` iff `o` is aligned to an `n` byte boundary.
    public func offset(_ o: Offset, hasAlignment n: Int) -> Bool {
      storage.withUnsafeBytes {
        UInt(bitPattern: $0.baseAddress! + baseOffset + o) % UInt(n) == 0
      }
    }
  }

  /// A memory location.
  public struct Address: Regular, CustomStringConvertible {

    /// The containing allocation.
    public let allocation: Allocation.ID

    /// The offset from the beginning of that `allocation`.
    public let offset: Storage.Index

    public var description: String { "@\(allocation):0x\(String(offset, radix: 16))" }

  }

  /// A typed location in memory.
  public struct TypedAddress: Regular, CustomStringConvertible {

    /// The containing allocation.
    public let allocation: Allocation.ID

    /// The offset from the beginning of that `allocation`.
    public let offset: Storage.Index

    /// The type to be accessed at `offset` in `allocation`.
    public let type: MonomorphicTypeIdentity

    public var description: String { "@\(allocation):0x\(String(offset, radix: 16))[\(type)]" }

  }

  /// Allocates `n` contiguous instances of `t` and returns the`Address` of the first instance.
  public mutating func allocate(_ t: MonomorphicTypeIdentity, count n: Int = 1) -> Address {
    let a = nextAllocation
    nextAllocation += 1
    allocation[a] = Allocation(typeLayouts.layout(t, in: &program), count: n, id: a)
    return .init(allocation: a, offset: 0)
  }

  /// Deallocates the allocation starting at `a`.
  public mutating func deallocate(_ a: Address) throws {
    if a.offset != 0 {
      throw Error.deallocationNotAtStartOfAllocation(a)
    }
    let v = allocation.removeValue(forKey: a.allocation)
    if v == nil {
      throw Error.noLongerAllocated(a)
    }
  }

  /// Returns true if `a` is aligned to an `n` byte boundary.
  public func address(_ a: Address, hasAlignment n: Int) -> Bool {
    allocation[a.allocation]!.offset(a.offset, hasAlignment: n)
  }

  /// The allocation identified by `i`.
  public subscript(_ i: Allocation.ID) -> Allocation {
    _read {
      yield allocation[i]!
    }
    _modify {
      yield &allocation[i]!
    }
  }
}

extension Memory.Address {

  /// Returns `l` offset by `r` bytes.
  static func + (l: Self, r: Int) -> Self {
    .init(allocation: l.allocation, offset: l.offset + r)
  }

  /// Returns `l` offset by `-r` bytes.
  static func - (l: Self, r: Int) -> Self {
    .init(allocation: l.allocation, offset: l.offset - r)
  }

  /// Returns `r` offset by `l` bytes.
  static func + (l: Int, r: Self) -> Self {
    .init(allocation: r.allocation, offset: l + r.offset)
  }

  ///  Offsets `l` by `r` bytes.
  static func += (l: inout Self, r: Int) { l = l + r }

  ///  Offsets `l` by `-r` bytes.
  static func -= (l: inout Self, r: Int) { l = l - r }

}

extension UnsafeRawPointer {

  /// Returns the number of bytes from `self` to the nearest address
  /// aligned to `a`.
  fileprivate func offsetToAlignment(_ a: Int) -> Int {
    let b = UInt(bitPattern: self)
    return Int(b.roundedUp(toNearestMultipleOf: UInt(a)) - b)
  }

}

extension UnsafeRawBufferPointer {

  /// Returns the number of bytes from the notional base address to
  /// the nearest address aligned to `a`.
  ///
  /// If `self.baseAddress == nil`, returns `0`.
  internal func firstOffsetAligned(to a: Int) -> Int {
    return baseAddress?.offsetToAlignment(a) ?? 0
  }

}

extension Memory {

  /// Allocates `n` contiguous instances of `t` and returns the`Address` of the first instance.
  ///
  /// - Precondition: `t` is a monomorphic type.
  public mutating func allocate(storageFor t: AnyTypeIdentity, count n: Int = 1) -> Address {
    allocate(.init(t), count: n)
  }

  /// Returns layout of `t`.
  public mutating func layout(_ t: MonomorphicTypeIdentity) -> TypeLayout {
    typeLayouts.layout(t, in: &program)
  }

  /// Returns the address of `subPart` in `whole`.
  public mutating func location(_ subPart: IndexPath, in whole: TypedAddress) -> TypedAddress {
    let (t, o) =
      typeLayouts.typeAndOffset(subPart, within: whole.type, definedIn: &program)
    return .init(allocation: whole.allocation, offset: o + whole.offset, type: t)
  }

  /// Stores `v` at `p`.
  ///
  /// - Precondition: `v` is an instance of type `p.type`.
  private mutating func store(_ v: RuntimeValue, at p: Memory.TypedAddress) {
    let n = v.bytes.count
    let o = p.offset
    self[p.allocation].storage[o..<o + n] = v.bytes
  }

  /// Stores `v` at `p`.
  ///
  /// - Precondition: `v` is an instance of type `p.location.type`.
  public mutating func store(_ v: RuntimeValue, at p: Access<Memory.TypedAddress>) throws {
    // TODO: throw if it is illegal to write to `p` using its permissions.
    // TODO: throw if location pointed by `p` is not fully uninitialized.
    store(v, at: p.location)
  }

}
