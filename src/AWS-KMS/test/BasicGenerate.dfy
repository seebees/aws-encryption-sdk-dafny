// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../src/Index.dfy"

module TestComAmazonawsKms {
  import Com.Amazonaws.Kms

  method {:test} BasicGenerate() {
    var keyId := "arn:aws:kms:us-west-2:658956600833:key/b3537ef1-d8dc-4780-9f5a-55776cbb2f7f";

    var client :- expect Kms.KMSClient();

    var keyLength := 32;

    var request := Kms.Types.GenerateDataKeyRequest(
      KeyId := keyId,
      EncryptionContext := Kms.Wrappers.None,
      NumberOfBytes := Kms.Wrappers.Some(keyLength as Kms.Types.NumberOfBytesType),
      KeySpec := Kms.Wrappers.None,
      GrantTokens := Kms.Wrappers.None
    );

    var ret := client.GenerateDataKey(request);

    expect(ret.Success?);

    var GenerateDataKeyResponse(CiphertextBlob, Plaintext, KeyId) := ret.value;

    expect Plaintext.Some?;
    expect |Plaintext.value| == keyLength;
  }
}