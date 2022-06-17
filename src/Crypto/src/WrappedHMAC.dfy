// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Model/AwsCryptographyPrimitivesTypes.dfy"
include "HKDF/HMAC.dfy"

module WrappedHMAC {
  import opened StandardLibrary
  import opened Wrappers
  import opened UInt = StandardLibrary.UInt
  import Types = AwsCryptographyPrimitivesTypes
  import HMAC

  method Digest(input: Types.HMacInput)
    returns  ( output: Result<seq<uint8>, Types.Error> )
  {
    var HMacInput(digestAlgorithm, key, message) := input;

    var hmac := new HMAC.HMac(digestAlgorithm);
    hmac.Init(key);
    hmac.Update(message);
    var value := hmac.GetResult();

    // Any runtime Need check go here

    return Success(value);
  }
}
