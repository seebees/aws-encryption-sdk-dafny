// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../StandardLibrary/StandardLibrary.dfy"
include "../StandardLibrary/UInt.dfy"
include "Model/Aws.Cryptography.Primitives.Exceptions.dfy"

module Random {
  import opened Wrappers
  import opened UInt = StandardLibrary.UInt
  import ExternRandom
  import Aws.Cryptography.Primitives.Exceptions

  method GenerateBytes(i: int32) returns (res: Result<seq<uint8>, Exceptions.IAwsCryptographicPrimitivesException>)
    requires 0 <= i
    ensures res.Success? ==> |res.value| == i as int
  {
    var result := ExternRandom.GenerateBytes(i);
    if result.Success? && |result.value| != i as int {
      var err := new Exceptions.AwsCryptographicPrimitivesError("Incorrect length from ExternRandom.");
      return Failure(err);
    }
    return result;
  }
}

module {:extern "ExternRandom"} ExternRandom {
  import opened Wrappers
  import opened UInt = StandardLibrary.UInt
  import Aws.Cryptography.Primitives.Exceptions

  method {:extern} GenerateBytes(i: int32) returns (res: Result<seq<uint8>, Exceptions.IAwsCryptographicPrimitivesException>)
}
