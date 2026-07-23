import ArgumentParser
import Demangler
import Foundation

/// Demangles Hylo mangled symbols found in input text.
@main struct CommandLine: ParsableCommand {

  /// Configuration for this command.
  public static let configuration = CommandConfiguration(
    commandName: "hylo-demangle", abstract: "Demangle Hylo mangled symbols found in input text.")

  /// Whether to print a symbol-by-symbol listing instead of rewriting the input text.
  @Flag(
    name: [.customLong("list")],
    help: "Print each demangled symbol on its own line.")
  private var listOnly: Bool = false

  /// Input text to scan. If empty, the command reads stdin.
  @Argument(help: "Input text to scan. Reads stdin when omitted.")
  private var inputText: [String] = []

  /// Creates a new instance with default options.
  public init() {}

  /// Executes the command.
  public func run() throws {
    let input = try sourceText()

    if listOnly {
      printDemangled(input)
    }
    else {
      printRewritten(input)
    }

  }

  /// Returns the text to scan, from arguments or stdin.
  private func sourceText() throws -> String {
    if !inputText.isEmpty {
      return inputText.joined(separator: " ")
    }

    let data = FileHandle.standardInput.readDataToEndOfFile()
    guard let text = String(data: data, encoding: .utf8) else {
      throw ValidationError("stdin is not valid UTF-8")
    }
    return text
  }

  /// Prints `input` with each matched mangled symbol replaced by its demangled form.
  private func printRewritten(_ input: String) {
    print(TextDemangler.rewrite(input), terminator: "")
  }

  /// Prints the demangled form of each matched mangled symbol in `input`.
  private func printDemangled(_ input: String) {
    for symbol in TextDemangler.symbols(in: input) {
      print("\(symbol.mangled) => \(symbol.demangled)")
    }
  }

}
