#include <memory>
#include <vector>

class ListOfExamples {
  std::vector<std::unique_ptr<int>> m;
  int a;
public:
  ListOfExamples() {
  }

};

class Working{
  public:
  int a;
  int b;

  Working() {
    a = 1;
    b = 2;
  }
};

int main() {
  ListOfExamples l;
  Working w;
  return 0;
}

// static inline std::vector<std::unique_ptr<int>> getExamples() {
//   std::vector<std::unique_ptr<int>> m;
//   m.push_back(std::make_unique<int>(1));
//   return m;
// }
