import XCTest

extension XCTestCase {

  /// The error thrown when an operation does not complete within its time allowance.
  struct TimedOut: Error {
    let exceedingSeconds: TimeInterval

    var localizedDescription: String {
      "Test exceeded \(exceedingSeconds)s."
    }
  }

  /// Runs `operation`, failing the test and throwing `TimedOut` if it does not complete within
  /// `timeout` seconds.
  func withTimeout<T: Sendable>(
    seconds timeout: TimeInterval = 30,
    _ operation: @escaping @Sendable () async throws -> T
  ) async throws -> T {
    let done = expectation(description: "operation completes within \(timeout)s")
    let task = Task {
      defer { done.fulfill() }
      return try await operation()
    }

    // The task's value is only awaited once it is known to have completed.
    let outcome = await XCTWaiter().fulfillment(of: [done], timeout: timeout)
    if outcome == .completed {
      return try await task.value
    } else {
      task.cancel()
      throw TimedOut(exceedingSeconds: timeout)
    }
  }

}
