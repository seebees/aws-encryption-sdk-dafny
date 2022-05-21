// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../StandardLibrary/StandardLibrary.dfy"
include "Model/Aws.Cryptography.PrimitivesAbstract.dfy"

module Digest {
  import opened Wrappers
  import opened UInt = StandardLibrary.UInt
  import Types = AwsCryptographyPrimitivesTypes
  import ExternDigest

  function method Length(digestAlgorithm: Types.DigestAlgorithm): nat
  {
    match digestAlgorithm
      case SHA_512 => 64
      case SHA_384 => 48
      case SHA_256 => 32
  }

  method Digest(input: Types.DigestInput)
    returns (res: Result<seq<uint8>, Types.Error>)
    ensures res.Success? ==> |res.value| == Length(input.digestAlgorithm)
  {
    var DigestInput(digestAlgorithm, message) := input;
    var value :- ExternDigest.Digest(digestAlgorithm, message);
    :- Need(
      |value| == Length(digestAlgorithm),
      Types.AwsCryptographicPrimitivesError("Incorrect length digest from ExternDigest.")
    );
    return Success(value);
  }
}

module {:extern "ExternDigest" } ExternDigest {
  import opened Wrappers
  import opened UInt = StandardLibrary.UInt
  import Types = AwsCryptographyPrimitivesTypes

  method {:extern } Digest(alg: Types.DigestAlgorithm, msg: seq<uint8>)
    returns (res: Result<seq<uint8>, Types.OpaqueError>)
}
