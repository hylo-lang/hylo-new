# Serialization

`hc` can archive Hylo modules after they have been compiled to IR, so that they can be (re)loaded later on without going through the front-end again.
An archive contains the original sources of the module, its typed syntax trees, and its refined IR.   
The IR may also have gone through optimization.

Note that the archiving system is specific to `hc` and not part of Hylo's specification.
The remainder of this document documents some implementation details.

## Identities

The representation of a program in the compiler involves three main recursive data structures, namely abstract syntax trees (AST), the type trees, and the static single assignment (SSA) intermediate representation (IR).
Each of these three data structures is essentially an enumeration implemented similarly.
Each case of the enumeration is represented by a struct whose instances are stored in some collection.
The position of an instance in that collection serves as an identity, which may be used to implement composition or aggregation.

These identities have some properties.
1. They are _stable_ throughout the compilation process. That is, the identity of an instance is never invalidated unless that instance is destroyed.
3. They are produced deterministically. That is, two runs of the compiler on the same input will assign the same identity to any particular instance. 
2. They are lightweight and fit into a 64-bit integer.

These properties present one important challenge for serialization.
If a module can be compiled in isolation and loaded into a program later, we must guarantee that an identity cannot be assigned to different instances.
To address this issue, identities are serialized as zero-based offsets and reconstructed in context during deserialization.
Consequently, the identity of an instance is not necessarily preserved by round-tripping serialization.
The only guarantee is that any modification to an identity is applied consistently when a module is read from an archive.  
