class Example {
  int a;
  int b;

public:
  Example(int a, int b) : a(a), b(b) {}
  // non-copyable
  Example(const Example&) = delete;
  Example& operator=(const Example&) = delete;

  // movable
  Example(Example&&) = default;
  Example& operator=(Example&&) = default;

  ~Example() = default;

  int sum() const;
};

int exampleFun(int a, int b);
