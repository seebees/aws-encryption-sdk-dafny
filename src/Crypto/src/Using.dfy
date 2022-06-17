include "Index.dfy"
include "../../StandardLibrary/StandardLibrary.dfy"

module TestUsing {
  import opened Wrappers
  import Aws.Cryptography.Primitives

  method TestWithFactoryClasses() returns (res: Result<(),Primitives.Types.Error>) {
    var primitives :- Primitives.AtomicPrimitives();
    var input := Primitives.Types.GenerateRandomBytesInput( length := 32);
    var data := primitives.GenerateRandomBytes(input);
  }

}