/// A valid path component on the host operating system.
protocol PathComponent {

}

protocol FileName: PathComponent {
  var `extension`: String? { get }
}

protocol RelativePath: Collection where Element == PathComponent {

}

/// Has at least one component
protocol RelativeFilePath: RelativePath {
  var fileName: PathComponent { get }
}


struct AbsoluteDirectoryPath {

  /// The absolute directory path.
  private var rawValue: String

  var components: PathComponents {
    let p = Substring(rawValue) // todo drop drive letter component
    PathComponents(path: rawValue)
  }

}

struct PathComponents: Collection {
  let path: Substring

}