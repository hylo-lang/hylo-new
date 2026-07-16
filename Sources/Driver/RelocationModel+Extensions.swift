import SwiftyLLVM

extension RelocationModel {

  /// The clang CLI argument for applying `self` as relocation model.
  public var asClangArgument: String? {
    switch self {
    case .default: nil
    case .pic: "-fPIC"
    case .static: "-fno-PIC"
    }
  }

}
