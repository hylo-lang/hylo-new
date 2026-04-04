# Deploymorphization

A function (or type) is polymorphic iff it accepts type parameters and monomorphic otherwise.
The implementation (aka definition) of a monomorphic function may feature uses of polymorphic constructs that have to be either monomorphized or existentialized before IR can be compiled
to machine code.
This transformation is referred to as *depolymorphization*.

Both monomorphization and existentialization essentially consist of creating a copy of the polymoprhic function.
In the former case, type arguments are simply substituted for their corresponding parameters. In the latter case, the type parameters are transformed into term parameters accepting type witnesses at run-time.
