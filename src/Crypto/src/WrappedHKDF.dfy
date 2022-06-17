// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "HKDF/HKDF.dfy"
include "HKDF/HMAC.dfy"
include "../Model/AwsCryptographyPrimitivesTypes.dfy"

/*
 * Implementation of the https://tools.ietf.org/html/rfc5869 HMAC-based key derivation function
 */
module WrappedHKDF {
  import opened Wrappers
  import opened UInt = StandardLibrary.UInt
  import Types = AwsCryptographyPrimitivesTypes
  import HMAC
  import HKDF

  method Extract(input: Types.HkdfExtractInput) returns (prk: seq<uint8>)
  {
    var HkdfExtractInput(digest, salt, ikm) := input;
  }

  method Expand(input: Types.HkdfExpandInput) returns (okm: seq<uint8>)
  {
    var HkdfExpandInput(digest, prk, info, expectedLength) := input;
  }

  /*
   * The RFC 5869 KDF. Outputs L bytes of output key material.
   */
  method Hkdf(input: Types.HkdfInput) returns (okm: seq<uint8>)
  {
    var HkdfInput(digest, salt, ikm, info, expectedLength) := input;

    // okm := HKDF.Hkdf(digest, salt, ikm, info, expectedLength);
  }
}
