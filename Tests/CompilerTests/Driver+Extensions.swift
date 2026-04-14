import Driver
import Foundation

extension Driver {

  /// Returns a temporary folder for caching compilation artifacts during testing, along with a
  /// closure to delete it.
  static func temporaryModuleCachePath() -> (url: URL, delete: @Sendable () -> Void) {
    let m = FileManager.default
    let u = try! m.url(
      for: .itemReplacementDirectory,
      in: .userDomainMask,
      appropriateFor: m.currentDirectoryURL,
      create: true)
    return (u, { try? FileManager.default.removeItem(at: u) })
  }

}
