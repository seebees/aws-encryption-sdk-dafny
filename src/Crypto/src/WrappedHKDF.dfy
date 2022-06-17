// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "HKDF/HKDF.dfy"
include "HKDF/HMAC.dfy"
include "Digest.dfy"
include "../Model/AwsCryptographyPrimitivesTypes.dfy"

/*
 * Implementation of the https://tools.ietf.org/html/rfc5869 HMAC-based key derivation function
 */
module WrappedHKDF {
  import opened Wrappers
  import opened UInt = StandardLibrary.UInt
  import StandardLibrary
  import Types = AwsCryptographyPrimitivesTypes
  import HMAC
  import HKDF
  import Digest

  method Extract(input: Types.HkdfExtractInput)
    returns (prk: seq<uint8>)
    requires (input.salt.None? || |input.salt.value| != 0)
    requires (|input.ikm| < INT32_MAX_LIMIT)
  {
    var HkdfExtractInput(digestAlgorithm, salt, ikm) := input;

    var hmac := new HMAC.HMac(digestAlgorithm);
    prk := HKDF.Extract(
      hmac,
      salt.UnwrapOr(StandardLibrary.Fill(0, Digest.Length(digestAlgorithm))),
      ikm,
      digestAlgorithm
    );
  }

  method Expand(input: Types.HkdfExpandInput)
    returns (okm: seq<uint8>)
    requires 1 <= input.expectedLength as int <= 255 * Digest.Length(input.digestAlgorithm)
    requires |input.info| < INT32_MAX_LIMIT
    requires Digest.Length(input.digestAlgorithm) == |input.prk|
  {
    var HkdfExpandInput(digestAlgorithm, prk, info, expectedLength) := input;

    var hmac := new HMAC.HMac(digestAlgorithm);
    var output, _ := HKDF.Expand(
      hmac,
      prk,
      info,
      expectedLength as int,
      digestAlgorithm
    );
  }

  /*
   * The RFC 5869 KDF. Outputs L bytes of output key material.
   */
  method Hkdf(input: Types.HkdfInput)
    returns (okm: seq<uint8>)
    requires 0 <= input.expectedLength as int <= 255 * Digest.Length(input.digestAlgorithm)
    requires (input.salt.None? || |input.salt.value| != 0)
    requires |input.info| < INT32_MAX_LIMIT
    requires |input.ikm| < INT32_MAX_LIMIT
  {
    var HkdfInput(digest, salt, ikm, info, expectedLength) := input;

    okm := HKDF.Hkdf(
      digest,
      salt,
      ikm,
      info,
      expectedLength as int
    );
  }
}
