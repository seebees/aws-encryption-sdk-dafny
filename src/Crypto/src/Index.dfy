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

module Aws.Cryptography.Primitives refines AwsCryptographyPrimitivesAbstract {
  import Random
  import AESEncryption
  import D = Digest
  import WrappedHMAC
  import WrappedHKDF

  function method DefaultConfig(): CryptoConfig {
    CryptoConfig()
  }

  method AtomicPrimitives(config: CryptoConfig)
		returns (res: Result<IAwsCryptographicPrimitivesClient,Error>)
  {
    var client := new AtomicPrimitivesServiceThing(config);
    return Success(client);
  }

  class AtomicPrimitivesServiceThing extends IAwsCryptographicPrimitivesClient {

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
      output := Random.GenerateBytes(input.length);
    }

    method Digest ( input: DigestInput )
      returns  ( output: Result<seq<uint8>, Error> )
      ensures DigestCalledWith (  input )
      ensures output.Success? ==> DigestSucceededWith (  input , output.value )
    {
      output := D.Digest(input);
    }

    method HMac ( input: HMacInput )
      returns  ( output: Result<seq<uint8>, Error> )
      ensures HMacCalledWith (  input )
      ensures output.Success? ==> HMacSucceededWith (  input , output.value )
    {
      output := WrappedHMAC.Digest(input);
    }

    method HkdfExpand ( input: HkdfExpandInput )
      returns  ( output: Result<seq<uint8>, Error> )
      ensures HkdfExpandCalledWith (  input )
      ensures output.Success? ==> HkdfExpandSucceededWith (  input , output.value )
    {

    }

    method HkdfExtract ( input: HkdfExtractInput )
      returns  ( output: Result<seq<uint8>, Error> )
      ensures HkdfExtractCalledWith (  input )
      ensures output.Success? ==> HkdfExtractSucceededWith (  input , output.value )
    {

    }

    method Hkdf ( input: HkdfInput )
      returns  ( output: Result<seq<uint8>, Error> )
      ensures HkdfCalledWith (  input )
      ensures output.Success? ==> HkdfSucceededWith (  input , output.value )
    {

    }

    method AESDecrypt ( input: AESDecryptInput )
      returns  ( output: Result<seq<uint8>, Error> )
      ensures AESDecryptCalledWith (  input )
      ensures output.Success? ==> AESDecryptSucceededWith (  input , output.value )
    {
      output := AESEncryption.AESDecrypt(input);
    }

    method AESEncrypt ( input: AESEncryptInput )
      returns  ( output: Result<AESEncryptOutput, Error> )
      ensures AESEncryptCalledWith (  input )
      ensures output.Success? ==> AESEncryptSucceededWith (  input , output.value )
      ensures output.Success? ==> AESEncryption.EncryptionOutputEncryptedWithAAD(output.value, input.aad)
    {
      output := AESEncryption.AESEncrypt(input);
    }
  }
}