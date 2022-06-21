// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../src/Index.dfy"
include "../../StandardLibrary/StandardLibrary.dfy"
include "../src/Digest.dfy"

module TestAwsCryptographyPrimitivesAES {
  import Aws.Cryptography.Primitives
  import opened Wrappers
  import opened StandardLibrary.UInt
  import Digest

  method {:test} AESDecryptTests() {

    BasicAESDecryptTest(
      Primitives.Types.AESDecryptInput(
        encAlg := Primitives.Types.AES_GCM(
          keyLength := 32,
          tagLength := 16,
          ivLength := 12
        ),
        key := [
          1, 1, 1, 1, 1, 1, 1, 1, 1,
          1, 1, 1, 1, 1, 1, 1, 1, 1,
          1, 1, 1, 1, 1, 1, 1, 1, 1,
          1, 1, 1, 1, 1
        ],
        cipherTxt := [ 102, 165, 173, 47 ],
        authTag := [
          54, 200,  18,  56, 172,
          194, 174,  23, 239, 151,
          47, 180, 143, 232, 142,
          184
        ],
        iv := [
          2, 2, 2, 2, 2,
          2, 2, 2, 2, 2,
          2, 2
        ],
        aad := [3,3,3,3]
      ),
      // The string "asdf" as bytes
      [ 97, 115, 100, 102 ]
    );

  }

  method {:test} AESEncryptTests() {
    BasicAESEncryptTest(
      Primitives.Types.AESEncryptInput(
        encAlg := Primitives.Types.AES_GCM(
          keyLength := 32,
          tagLength := 16,
          ivLength := 12
        ),
        iv := [
          2, 2, 2, 2, 2,
          2, 2, 2, 2, 2,
          2, 2
        ],
        key := [
          1, 1, 1, 1, 1, 1, 1, 1, 1,
          1, 1, 1, 1, 1, 1, 1, 1, 1,
          1, 1, 1, 1, 1, 1, 1, 1, 1,
          1, 1, 1, 1, 1
        ],
        // The string "asdf" as bytes
        msg := [ 97, 115, 100, 102 ],
        aad := [3,3,3,3]
      )
    );
  }

  method BasicAESDecryptTest(
    input: Primitives.Types.AESDecryptInput,
    expectedOutput: seq<uint8>
  )
  {
    var client :- expect Primitives.Crypto();
    var output :- expect client.AESDecrypt(input);
    expect output == expectedOutput;
  }

  method BasicAESEncryptTest(
    input: Primitives.Types.AESEncryptInput
  )
  {
    var client :- expect Primitives.Crypto();
    var output :- expect client.AESEncrypt(input);

    var decryptInput := Primitives.Types.AESDecryptInput(
      encAlg := input.encAlg,
      key := input.key,
      cipherTxt := output.cipherText,
      authTag := output.authTag,
      iv := input.iv,
      aad := input.aad
    );

    BasicAESDecryptTest(decryptInput, input.msg);
  }
}
