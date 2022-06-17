// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Model/AwsCryptographyPrimitivesTypes.dfy"
include "Random.dfy"
include "WrappedHMAC.dfy"
include "WrappedHKDF.dfy"
include "AESEncryption.dfy"
include "Digest.dfy"
include "RSAEncryption.dfy"
include "Signature.dfy"

module {:extern "Dafny.Aws.Cryptography.Primitives" } Aws.Cryptography.Primitives refines AwsCryptographyPrimitivesAbstract {
  import Random
  import AESEncryption
  import D = Digest
  import WrappedHMAC
  import WrappedHKDF

  function method DefaultCryptoConfig(): CryptoConfig {
    CryptoConfig()
  }

  method Crypto(config: CryptoConfig)
		returns (res: Result<IAwsCryptographicPrimitivesClient,Error>)
  {
    var client := new AtomicPrimitivesClient(config);
    return Success(client);
  }

  class AtomicPrimitivesClient extends IAwsCryptographicPrimitivesClient {

    const config: CryptoConfig
    constructor(config: CryptoConfig)
    {
      this.config := config;
    }

    method GenerateRandomBytes ( input: GenerateRandomBytesInput )
      returns  ( output: Result<seq<uint8>, Error> )
      ensures GenerateRandomBytesCalledWith (  input )
      ensures output.Success? ==> GenerateRandomBytesSucceededWith (  input , output.value )
    {
      AssumeGenerateRandomBytesCalledWith(input);
      var value :- Random.GenerateBytes(input.length);
      AssumeGenerateRandomBytesSucceededWith(input , value);
      output := Success(value);
    }

    method Digest ( input: DigestInput )
      returns  ( output: Result<seq<uint8>, Error> )
      ensures DigestCalledWith (  input )
      ensures output.Success? ==> DigestSucceededWith (  input , output.value )
    {
      AssumeDigestCalledWith(input);
      var value :- D.Digest(input);
      AssumeDigestSucceededWith(input, value);
      output := Success(value);
    }

    method HMac ( input: HMacInput )
      returns  ( output: Result<seq<uint8>, Error> )
      ensures HMacCalledWith (  input )
      ensures output.Success? ==> HMacSucceededWith (  input , output.value )
    {
      AssumeHMacCalledWith(input);
      var value :- WrappedHMAC.Digest(input);
      AssumeHMacSucceededWith(input, value);
      output := Success(value);
    }

    method HkdfExtract ( input: HkdfExtractInput )
      returns  ( output: Result<seq<uint8>, Error> )
      ensures HkdfExtractCalledWith (  input )
      ensures output.Success? ==> HkdfExtractSucceededWith (  input , output.value )
    {

      AssumeHkdfExtractCalledWith(input);

      :- Need(
        && (input.salt.None? || |input.salt.value| != 0)
        && |input.ikm| < INT32_MAX_LIMIT,
        Types.AwsCryptographicPrimitivesError(message := "No.")
      );

      var value := WrappedHKDF.Extract(input);
      AssumeHkdfExtractSucceededWith(input, value);
      output := Success(value);
    }

    method HkdfExpand ( input: HkdfExpandInput )
      returns  ( output: Result<seq<uint8>, Error> )
      ensures HkdfExpandCalledWith (  input )
      ensures output.Success? ==> HkdfExpandSucceededWith (  input , output.value )
    {
      AssumeHkdfExpandCalledWith(input);

      :- Need(
        && 1 <= input.expectedLength as int <= 255 * D.Length(input.digestAlgorithm)
        && |input.info| < INT32_MAX_LIMIT
        && D.Length(input.digestAlgorithm) == |input.prk|,
        Types.AwsCryptographicPrimitivesError(message := "No.")
      );

      var value := WrappedHKDF.Expand(input);
      AssumeHkdfExpandSucceededWith(input, value);
      output := Success(value);
    }

    method Hkdf ( input: HkdfInput )
      returns  ( output: Result<seq<uint8>, Error> )
      ensures HkdfCalledWith (  input )
      ensures output.Success? ==> HkdfSucceededWith (  input , output.value )
    {
      AssumeHkdfCalledWith(input);

      :- Need(
        && 0 <= input.expectedLength as int <= 255 * D.Length(input.digestAlgorithm)
        && (input.salt.None? || |input.salt.value| != 0)
        && |input.info| < INT32_MAX_LIMIT
        && |input.ikm| < INT32_MAX_LIMIT,
        Types.AwsCryptographicPrimitivesError(message := "No.")
      );

      var value := WrappedHKDF.Hkdf(input);
      AssumeHkdfSucceededWith(input, value);
      output := Success(value);
    }

    method AESDecrypt ( input: AESDecryptInput )
      returns  ( output: Result<seq<uint8>, Error> )
      ensures AESDecryptCalledWith (  input )
      ensures output.Success? ==> AESDecryptSucceededWith (  input , output.value )
    {
      AssumeAESDecryptCalledWith(input);
      :- Need(
        && |input.key| == input.encAlg.keyLength as int
        && |input.iv| == input.encAlg.ivLength as int
        && |input.authTag| == input.encAlg.tagLength as int,
        Types.AwsCryptographicPrimitivesError(message := "Request does not match algorithm.")
      );

      var value :- AESEncryption.AESDecrypt(input);
      AssumeAESDecryptSucceededWith(input, value);
      output := Success(value);
    }

    method AESEncrypt ( input: AESEncryptInput )
      returns  ( output: Result<AESEncryptOutput, Error> )
      ensures AESEncryptCalledWith (  input )
      ensures output.Success? ==> AESEncryptSucceededWith (  input , output.value )
      ensures output.Success? ==> AESEncryption.EncryptionOutputEncryptedWithAAD(output.value, input.aad)
    {
      AssumeAESEncryptCalledWith(input);
      :- Need(
        && |input.iv| == input.encAlg.ivLength as int
        && |input.key| == input.encAlg.keyLength as int,
        Types.AwsCryptographicPrimitivesError(message := "Request does not match algorithm.")
      );

      var value :- AESEncryption.AESEncrypt(input);
      AssumeAESEncryptSucceededWith(input, value);
      output := Success(value);
    }
  }
}
