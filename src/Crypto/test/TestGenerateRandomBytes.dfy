// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../src/Index.dfy"
include "../../StandardLibrary/StandardLibrary.dfy"

module TestAwsCryptographyPrimitivesGenerateRandomBytes {
  import Aws.Cryptography.Primitives
  import opened StandardLibrary.UInt

  method {:test} BasicGenerateRandomBytes() {
    var client :- expect Primitives.Crypto();
    var length := 5 as int32;
    assert Primitives.Types.IsValid_PositiveInteger(length);

    var input := Primitives.Types.GenerateRandomBytesInput(
      length := length
    );

    var value :- expect client.GenerateRandomBytes(input);

    expect |value| == length as int;
  }
}