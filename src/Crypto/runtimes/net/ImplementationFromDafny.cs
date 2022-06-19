// Dafny program the_program compiled into C#
// To recompile, you will need the libraries
//     System.Runtime.Numerics.dll System.Collections.Immutable.dll
// but the 'dotnet' tool in net6.0 should pick those up automatically.
// Optionally, you may want to include compiler switches like
//     /debug /nowarn:162,164,168,183,219,436,1717,1718

using System;
using System.Numerics;
[assembly: DafnyAssembly.DafnySourceAttribute(@"// Dafny 3.6.0.40511
// Command Line Options: /compileTarget:cs /spillTargetCode:3 /compile:0 /out runtimes/net/ImplementationFromDafny src/HKDF/HKDF.dfy src/HKDF/HMAC.dfy src/AESEncryption.dfy src/Digest.dfy src/Index.dfy src/RSAEncryption.dfy src/Random.dfy src/Signature.dfy src/WrappedHKDF.dfy src/WrappedHMAC.dfy
// the_program


module HKDF {

  import opened HMAC

  import opened Wrappers

  import opened UInt = StandardLibrary.UInt

  import Types = AwsCryptographyPrimitivesTypes

  import Digest
  method Extract(hmac: HMac, salt: seq<uint8>, ikm: seq<uint8>, ghost digest: Types.DigestAlgorithm)
      returns (prk: seq<uint8>)
    requires hmac.GetDigest() == digest
    requires |salt| != 0
    requires |ikm| < INT32_MAX_LIMIT
    modifies hmac
    ensures Digest.Length(hmac.GetDigest()) == |prk|
    ensures hmac.GetKey() == salt
    ensures hmac.GetDigest() == digest
    decreases hmac, salt, ikm, digest
  {
    hmac.Init(salt);
    hmac.Update(ikm);
    assert hmac.GetInputSoFar() == ikm;
    prk := hmac.GetResult();
    return prk;
  }

  predicate T(hmac: HMac, info: seq<uint8>, n: nat, res: seq<uint8>)
    requires 0 <= n < 256
    decreases n
  {
    if n == 0 then
      [] == res
    else
      ghost var nMinusOne: int := n - 1; exists prev1: seq<uint8>, prev2: seq<uint8> :: T(hmac, info, nMinusOne, prev1) && Ti(hmac, info, n, prev2) && prev1 + prev2 == res
  }

  predicate Ti(hmac: HMac, info: seq<uint8>, n: nat, res: seq<uint8>)
    requires 0 <= n < 256
    decreases n, 1
  {
    if n == 0 then
      res == []
    else
      exists prev: seq<uint8> :: PreTi(hmac, info, n, prev) && hmac.HashSignature(prev, res)
  }

  predicate PreTi(hmac: HMac, info: seq<uint8>, n: nat, res: seq<uint8>)
    requires 1 <= n < 256
    decreases n, 0
  {
    ghost var nMinusOne: int := n - 1;
    exists prev: seq<uint8> | Ti(hmac, info, nMinusOne, prev) :: 
      res == prev + info + [n as uint8]
  }

  method Expand(hmac: HMac, prk: seq<uint8>, info: seq<uint8>, expectedLength: int, digest: Types.DigestAlgorithm)
      returns (okm: seq<uint8>, ghost okmUnabridged: seq<uint8>)
    requires hmac.GetDigest() == digest
    requires 1 <= expectedLength <= 255 * Digest.Length(hmac.GetDigest())
    requires |info| < INT32_MAX_LIMIT
    requires Digest.Length(hmac.GetDigest()) == |prk|
    modifies hmac
    ensures |okm| == expectedLength
    ensures hmac.GetKey() == prk
    ensures hmac.GetDigest() == digest
    ensures var n: int := (Digest.Length(digest) + expectedLength - 1) / Digest.Length(digest); T(hmac, info, n, okmUnabridged) && (|okmUnabridged| <= expectedLength ==> okm == okmUnabridged) && (expectedLength < |okmUnabridged| ==> okm == okmUnabridged[..expectedLength])
    decreases hmac, prk, info, expectedLength, digest
  {
    var hashLength := Digest.Length(digest);
    var n := (hashLength + expectedLength - 1) / hashLength;
    assert 0 <= n < 256;
    hmac.Init(prk);
    var t_prev := [];
    var t_n := t_prev;
    var i := 1;
    while i <= n
      invariant 1 <= i <= n + 1
      invariant |t_prev| == if i == 1 then 0 else hashLength
      invariant hashLength == |prk|
      invariant |t_n| == (i - 1) * hashLength
      invariant hmac.GetKey() == prk
      invariant hmac.GetDigest() == digest
      invariant hmac.GetInputSoFar() == []
      invariant T(hmac, info, i - 1, t_n)
      invariant Ti(hmac, info, i - 1, t_prev)
      decreases n - i
    {
      hmac.Update(t_prev);
      hmac.Update(info);
      hmac.Update([i as uint8]);
      assert hmac.GetInputSoFar() == t_prev + info + [i as uint8];
      t_prev := hmac.GetResult();
      assert Ti(hmac, info, i, t_prev);
      t_n := t_n + t_prev;
      i := i + 1;
      assert T(hmac, info, i - 1, t_n);
    }
    okm := t_n;
    okmUnabridged := okm;
    assert T(hmac, info, n, okmUnabridged);
    if expectedLength < |okm| {
      okm := okm[..expectedLength];
    }
  }

  method Hkdf(digest: Types.DigestAlgorithm, salt: Option<seq<uint8>>, ikm: seq<uint8>, info: seq<uint8>, L: int)
      returns (okm: seq<uint8>)
    requires 0 <= L <= 255 * Digest.Length(digest)
    requires salt.None? || |salt.value| != 0
    requires |info| < INT32_MAX_LIMIT
    requires |ikm| < INT32_MAX_LIMIT
    ensures |okm| == L
    decreases digest, salt, ikm, info, L
  {
    if L == 0 {
      return [];
    }
    var hmac := new HMac(digest);
    var hashLength := Digest.Length(digest);
    var nonEmptySalt: seq<uint8>;
    match salt {
      case {:split false} None() =>
        nonEmptySalt := StandardLibrary.Fill(0, hashLength);
      case {:split false} Some(s) =>
        nonEmptySalt := s;
    }
    var prk := Extract(hmac, nonEmptySalt, ikm, digest);
    ghost var okmUnabridged;
    okm, okmUnabridged := Expand(hmac, prk, info, L, digest);
  }
}

module {:extern ""HMAC""} HMAC {

  import opened StandardLibrary

  import opened UInt = StandardLibrary.UInt

  import Types = AwsCryptographyPrimitivesTypes

  import Digest
  class {:extern ""HMac""} HMac {
    function {:extern} GetKey(): seq<uint8>
      reads this
      decreases {this}

    function {:extern} GetDigest(): Types.DigestAlgorithm
      reads this
      decreases {this}

    function {:extern} GetInputSoFar(): seq<uint8>
      reads this
      decreases {this}

    constructor {:extern} (digest: Types.DigestAlgorithm)
      ensures this.GetDigest() == digest
      ensures this.GetInputSoFar() == []
      decreases digest

    method {:extern ""Init""} Init(key: seq<uint8>)
      modifies this
      ensures this.GetKey() == key
      ensures this.GetDigest() == old(this.GetDigest())
      ensures this.GetInputSoFar() == []
      decreases key

    method {:extern ""BlockUpdate""} Update(input: seq<uint8>)
      requires |this.GetKey()| > 0
      requires |input| < INT32_MAX_LIMIT
      modifies this
      ensures this.GetInputSoFar() == old(this.GetInputSoFar()) + input
      ensures this.GetDigest() == old(this.GetDigest())
      ensures this.GetKey() == old(this.GetKey())
      decreases input

    method {:extern ""GetResult""} GetResult() returns (s: seq<uint8>)
      requires |this.GetKey()| > 0
      modifies this
      ensures |s| == Digest.Length(this.GetDigest())
      ensures this.GetInputSoFar() == []
      ensures this.GetDigest() == old(this.GetDigest())
      ensures this.GetKey() == old(this.GetKey())
      ensures this.HashSignature(old(this.GetInputSoFar()), s)

    predicate {:axiom} HashSignature(message: seq<uint8>, s: seq<uint8>)
      decreases message, s
  }
}

module {:extern ""AESEncryption""} AESEncryption {

  import opened Wrappers

  import opened UInt = StandardLibrary.UInt

  import Types = AwsCryptographyPrimitivesTypes
  predicate {:axiom} PlaintextDecryptedWithAAD(plaintext: seq<uint8>, aad: seq<uint8>)
    decreases plaintext, aad

  predicate {:axiom} EncryptionOutputEncryptedWithAAD(output: Types.AESEncryptOutput, aad: seq<uint8>)
    decreases output, aad

  predicate {:axiom} CiphertextGeneratedWithPlaintext(ciphertext: seq<uint8>, plaintext: seq<uint8>)
    decreases ciphertext, plaintext

  predicate {:axiom} EncryptedWithKey(ciphertext: seq<uint8>, key: seq<uint8>)
    decreases ciphertext, key

  predicate {:axiom} DecryptedWithKey(key: seq<uint8>, plaintext: seq<uint8>)
    decreases key, plaintext

  function method EncryptionOutputFromByteSeq(s: seq<uint8>, encAlg: Types.AES_GCM): (encArt: Types.AESEncryptOutput)
    requires 0 < encAlg.tagLength
    requires encAlg.tagLength as nat <= |s|
    ensures |encArt.cipherText + encArt.authTag| == |s|
    ensures |encArt.authTag| == encAlg.tagLength as int
    decreases s, encAlg
  {
    assert |s| - encAlg.tagLength as int <= |s|;
    var cipherText: seq<uint8> := s[..|s| - encAlg.tagLength as int];
    var authTag: seq<uint8> := s[|s| - encAlg.tagLength as int..];
    Types.AESEncryptOutput(cipherText := cipherText, authTag := authTag)
  }

  method {:extern ""AESEncryption.AES_GCM"", ""AESEncryptExtern""} AESEncryptExtern(encAlg: Types.AES_GCM, iv: seq<uint8>, key: seq<uint8>, msg: seq<uint8>, aad: seq<uint8>)
      returns (res: Result<Types.AESEncryptOutput, Types.OpaqueError>)
    requires |iv| == encAlg.ivLength as int
    requires |key| == encAlg.keyLength as int
    ensures res.Success? ==> EncryptionOutputEncryptedWithAAD(res.value, aad)
    ensures res.Success? ==> CiphertextGeneratedWithPlaintext(res.value.cipherText, msg)
    ensures res.Success? ==> EncryptedWithKey(res.value.cipherText, key)
    decreases encAlg, iv, key, msg, aad

  method AESEncrypt(input: Types.AESEncryptInput) returns (res: Result<Types.AESEncryptOutput, Types.Error>)
    requires |input.iv| == input.encAlg.ivLength as int
    requires |input.key| == input.encAlg.keyLength as int
    ensures res.Success? ==> |res.value.cipherText| == |input.msg| && |res.value.authTag| == input.encAlg.tagLength as int
    ensures res.Success? ==> EncryptionOutputEncryptedWithAAD(res.value, input.aad)
    ensures res.Success? ==> CiphertextGeneratedWithPlaintext(res.value.cipherText, input.msg)
    ensures res.Success? ==> EncryptedWithKey(res.value.cipherText, input.key)
    ensures res.Success? ==> |res.value.authTag| == input.encAlg.tagLength as nat
    decreases input
  {
    var AESEncryptInput(encAlg, iv, key, msg, aad) := input;
    var value :- AESEncryptExtern(encAlg, iv, key, msg, aad);
    :- Need(|value.cipherText| == |msg|, Types.AwsCryptographicPrimitivesError(message := ""AESEncrypt did not return cipherText of expected length""));
    :- Need(|value.authTag| == encAlg.tagLength as int, Types.AwsCryptographicPrimitivesError(message := ""AESEncryption did not return valid tag""));
    return Success(value);
  }

  method {:extern ""AESEncryption.AES_GCM"", ""AESDecryptExtern""} AESDecryptExtern(encAlg: Types.AES_GCM, key: seq<uint8>, cipherTxt: seq<uint8>, authTag: seq<uint8>, iv: seq<uint8>, aad: seq<uint8>)
      returns (res: Result<seq<uint8>, Types.OpaqueError>)
    requires |key| == encAlg.keyLength as int
    requires |iv| == encAlg.ivLength as int
    requires |authTag| == encAlg.tagLength as int
    ensures res.Success? ==> PlaintextDecryptedWithAAD(res.value, aad)
    ensures res.Success? ==> CiphertextGeneratedWithPlaintext(cipherTxt, res.value)
    ensures res.Success? ==> DecryptedWithKey(key, res.value)
    decreases encAlg, key, cipherTxt, authTag, iv, aad

  method AESDecrypt(input: Types.AESDecryptInput) returns (res: Result<seq<uint8>, Types.Error>)
    requires |input.key| == input.encAlg.keyLength as int
    requires |input.iv| == input.encAlg.ivLength as int
    requires |input.authTag| == input.encAlg.tagLength as int
    ensures res.Success? ==> |res.value| == |input.cipherTxt|
    ensures res.Success? ==> PlaintextDecryptedWithAAD(res.value, input.aad)
    ensures res.Success? ==> CiphertextGeneratedWithPlaintext(input.cipherTxt, res.value)
    ensures res.Success? ==> DecryptedWithKey(input.key, res.value)
    decreases input
  {
    var AESDecryptInput(encAlg, key, cipherTxt, authTag, iv, aad) := input;
    var value :- AESDecryptExtern(encAlg, key, cipherTxt, authTag, iv, aad);
    :- Need(|cipherTxt| == |value|, Types.AwsCryptographicPrimitivesError(message := ""AESDecrypt did not return plaintext of expected length""));
    return Success(value);
  }
}

module Digest {

  import opened Wrappers

  import opened UInt = StandardLibrary.UInt

  import Types = AwsCryptographyPrimitivesTypes

  import ExternDigest
  function method Length(digestAlgorithm: Types.DigestAlgorithm): nat
    decreases digestAlgorithm
  {
    match digestAlgorithm
    case SHA_512() =>
      64
    case SHA_384() =>
      48
    case SHA_256() =>
      32
  }

  method Digest(input: Types.DigestInput) returns (res: Result<seq<uint8>, Types.Error>)
    ensures res.Success? ==> |res.value| == Length(input.digestAlgorithm)
    decreases input
  {
    var DigestInput(digestAlgorithm, message) := input;
    var value :- ExternDigest.Digest(digestAlgorithm, message);
    :- Need(|value| == Length(digestAlgorithm), Types.AwsCryptographicPrimitivesError(message := ""Incorrect length digest from ExternDigest.""));
    return Success(value);
  }
}

module {:extern ""ExternDigest""} ExternDigest {

  import opened Wrappers

  import opened UInt = StandardLibrary.UInt

  import Types = AwsCryptographyPrimitivesTypes
  method {:extern} Digest(alg: Types.DigestAlgorithm, msg: seq<uint8>) returns (res: Result<seq<uint8>, Types.OpaqueError>)
    decreases alg, msg
}

module {:extern ""RSAEncryption""} RSAEncryption {

  import opened Wrappers

  import opened UInt = StandardLibrary.UInt
  datatype {:extern ""PaddingMode""} PaddingMode = PKCS1 | OAEP_SHA1 | OAEP_SHA256 | OAEP_SHA384 | OAEP_SHA512

  newtype {:nativeType ""int"", ""number""} StrengthBits = x: int
    | 81 <= x < 2147483648
    witness 81

  trait {:termination false} Key {
    const strength: StrengthBits
    const pem: seq<uint8>

    predicate Valid()
    {
      |pem| > 0
    }
  }

  class PrivateKey extends Key {
    constructor (pem: seq<uint8>, strength: StrengthBits)
      requires |pem| > 0
      ensures this.pem == pem
      ensures this.strength == strength
      ensures Valid()
      decreases pem, strength
    {
      this.pem := pem;
      this.strength := strength;
    }
  }

  class PublicKey extends Key {
    constructor (pem: seq<uint8>, strength: StrengthBits)
      requires |pem| > 0
      ensures this.pem == pem
      ensures this.strength == strength
      ensures Valid()
      decreases pem, strength
    {
      this.pem := pem;
      this.strength := strength;
    }
  }

  method GenerateKeyPair(strength: StrengthBits) returns (publicKey: PublicKey, privateKey: PrivateKey)
    ensures privateKey.Valid()
    ensures publicKey.Valid()
    decreases strength
  {
    var pemPublic, pemPrivate := GenerateKeyPairExtern(strength);
    privateKey := new PrivateKey(pemPrivate, strength);
    publicKey := new PublicKey(pemPublic, strength);
  }

  method {:extern ""RSAEncryption.RSA"", ""GenerateKeyPairExtern""} GenerateKeyPairExtern(strength: StrengthBits) returns (publicKey: seq<uint8>, privateKey: seq<uint8>)
    ensures |publicKey| > 0
    ensures |privateKey| > 0
    decreases strength

  method {:extern ""RSAEncryption.RSA"", ""DecryptExtern""} DecryptExtern(padding: PaddingMode, privateKey: seq<uint8>, cipherText: seq<uint8>)
      returns (res: Result<seq<uint8>, string>)
    requires |privateKey| > 0
    requires |cipherText| > 0
    decreases padding, privateKey, cipherText

  method {:extern ""RSAEncryption.RSA"", ""EncryptExtern""} EncryptExtern(padding: PaddingMode, publicKey: seq<uint8>, plaintextData: seq<uint8>)
      returns (res: Result<seq<uint8>, string>)
    requires |publicKey| > 0
    requires |plaintextData| > 0
    decreases padding, publicKey, plaintextData
}

module Random {

  import opened Wrappers

  import opened UInt = StandardLibrary.UInt

  import ExternRandom

  import Types = AwsCryptographyPrimitivesTypes
  method GenerateBytes(i: int32) returns (res: Result<seq<uint8>, Types.Error>)
    requires 0 <= i
    ensures res.Success? ==> |res.value| == i as int
    decreases i
  {
    var value :- ExternRandom.GenerateBytes(i);
    :- Need(|value| == i as int, Types.AwsCryptographicPrimitivesError(message := ""Incorrect length from ExternRandom.""));
    return Success(value);
  }
}

module {:extern ""ExternRandom""} ExternRandom {

  import opened Wrappers

  import opened UInt = StandardLibrary.UInt

  import Types = AwsCryptographyPrimitivesTypes
  method {:extern} GenerateBytes(i: int32) returns (res: Result<seq<uint8>, Types.OpaqueError>)
    decreases i
}

module {:extern ""Signature""} Signature {

  export
    reveals SignatureKeyPair, ECDSAParams, ECDSAParams.SignatureLength, ECDSAParams.FieldSize
    provides KeyGen, Sign, Verify, IsSigned, IsValidSignatureKeyPair, Wrappers, UInt, Types


  import opened Wrappers

  import opened UInt = StandardLibrary.UInt

  import Types = AwsCryptographyPrimitivesTypes
  datatype SignatureKeyPair = SignatureKeyPair(verificationKey: seq<uint8>, signingKey: seq<uint8>)

  datatype ECDSAParams = ECDSA_P384 | ECDSA_P256 {
    function method SignatureLength(): uint16
      decreases this
    {
      match this
      case ECDSA_P256() =>
        71
      case ECDSA_P384() =>
        103
    }

    function method FieldSize(): nat
      decreases this
    {
      match this
      case ECDSA_P256() =>
        assert 1 + (256 + 7) / 8 == 33; 33
      case ECDSA_P384() =>
        assert 1 + (384 + 7) / 8 == 49;
        49
    }
  }

  predicate {:axiom} IsSigned(key: seq<uint8>, msg: seq<uint8>, signature: seq<uint8>)
    decreases key, msg, signature

  predicate {:axiom} IsValidSignatureKeyPair(sigKeyPair: SignatureKeyPair)
    decreases sigKeyPair

  method KeyGen(s: ECDSAParams) returns (res: Result<SignatureKeyPair, Types.Error>)
    ensures match res { case Success(_mcc#0: SignatureKeyPair) => (var sigKeyPair := _mcc#0; |sigKeyPair.verificationKey| == s.FieldSize() && IsValidSignatureKeyPair(sigKeyPair)) case Failure(_mcc#1: Types.Error) => true }
    decreases s
  {
    var sigKeyPair :- ExternKeyGen(s);
    if |sigKeyPair.verificationKey| == s.FieldSize() {
      return Success(sigKeyPair);
    } else {
      return Failure(Types.AwsCryptographicPrimitivesError(message := ""Incorrect verification-key length from ExternKeyGen.""));
    }
  }

  method {:extern ""Signature.ECDSA"", ""ExternKeyGen""} ExternKeyGen(s: ECDSAParams) returns (res: Result<SignatureKeyPair, Types.Error>)
    ensures res.Success? ==> IsValidSignatureKeyPair(res.value)
    decreases s

  method {:extern ""Signature.ECDSA"", ""Sign""} Sign(s: ECDSAParams, key: seq<uint8>, msg: seq<uint8>)
      returns (sig: Result<seq<uint8>, Types.Error>)
    ensures sig.Success? ==> IsSigned(key, msg, sig.value)
    decreases s, key, msg

  function method {:extern ""Signature.ECDSA"", ""Verify""} Verify(s: ECDSAParams, key: seq<uint8>, msg: seq<uint8>, sig: seq<uint8>): (res: Result<bool, Types.Error>)
    decreases s, key, msg, sig
}

module WrappedHKDF {

  import opened Wrappers

  import opened UInt = StandardLibrary.UInt

  import StandardLibrary

  import Types = AwsCryptographyPrimitivesTypes

  import HMAC

  import HKDF

  import Digest
  method Extract(input: Types.HkdfExtractInput) returns (prk: seq<uint8>)
    requires input.salt.None? || |input.salt.value| != 0
    requires |input.ikm| < INT32_MAX_LIMIT
    decreases input
  {
    var HkdfExtractInput(digestAlgorithm, salt, ikm) := input;
    var hmac := new HMAC.HMac(digestAlgorithm);
    prk := HKDF.Extract(hmac, salt.UnwrapOr(StandardLibrary.Fill(0, Digest.Length(digestAlgorithm))), ikm, digestAlgorithm);
  }

  method Expand(input: Types.HkdfExpandInput) returns (okm: seq<uint8>)
    requires 1 <= input.expectedLength as int <= 255 * Digest.Length(input.digestAlgorithm)
    requires |input.info| < INT32_MAX_LIMIT
    requires Digest.Length(input.digestAlgorithm) == |input.prk|
    decreases input
  {
    var HkdfExpandInput(digestAlgorithm, prk, info, expectedLength) := input;
    var hmac := new HMAC.HMac(digestAlgorithm);
    var output, _ := HKDF.Expand(hmac, prk, info, expectedLength as int, digestAlgorithm);
  }

  method Hkdf(input: Types.HkdfInput) returns (okm: seq<uint8>)
    requires 0 <= input.expectedLength as int <= 255 * Digest.Length(input.digestAlgorithm)
    requires input.salt.None? || |input.salt.value| != 0
    requires |input.info| < INT32_MAX_LIMIT
    requires |input.ikm| < INT32_MAX_LIMIT
    decreases input
  {
    var HkdfInput(digest, salt, ikm, info, expectedLength) := input;
    okm := HKDF.Hkdf(digest, salt, ikm, info, expectedLength as int);
  }
}

module WrappedHMAC {

  import opened StandardLibrary

  import opened Wrappers

  import opened UInt = StandardLibrary.UInt

  import Types = AwsCryptographyPrimitivesTypes

  import HMAC
  method Digest(input: Types.HMacInput) returns (output: Result<seq<uint8>, Types.Error>)
    decreases input
  {
    var HMacInput(digestAlgorithm, key, message) := input;
    :- Need(0 < |key|, Types.AwsCryptographicPrimitivesError(message := ""Key MUST NOT be 0 bytes.""));
    :- Need(|message| < INT32_MAX_LIMIT, Types.AwsCryptographicPrimitivesError(message := ""Message over INT32_MAX_LIMIT""));
    var hmac := new HMAC.HMac(digestAlgorithm);
    hmac.Init(key);
    hmac.Update(message);
    var value := hmac.GetResult();
    return Success(value);
  }
}

module {:extern ""Dafny.Aws.Cryptography.Primitives.Types""} AwsCryptographyPrimitivesTypes {

  import opened Wrappers

  import opened UInt = StandardLibrary.UInt

  import opened UTF8
  datatype AES_GCM = AES_GCM(nameonly keyLength: int32, nameonly tagLength: int32, nameonly ivLength: int32)

  datatype AESDecryptInput = AESDecryptInput(nameonly encAlg: AES_GCM, nameonly key: seq<uint8>, nameonly cipherTxt: seq<uint8>, nameonly authTag: seq<uint8>, nameonly iv: seq<uint8>, nameonly aad: seq<uint8>)

  datatype AESEncryptInput = AESEncryptInput(nameonly encAlg: AES_GCM, nameonly iv: seq<uint8>, nameonly key: seq<uint8>, nameonly msg: seq<uint8>, nameonly aad: seq<uint8>)

  datatype AESEncryptOutput = AESEncryptOutput(nameonly cipherText: seq<uint8>, nameonly authTag: seq<uint8>)

  trait {:termination false} IAwsCryptographicPrimitivesClient {
    method GenerateRandomBytes(input: GenerateRandomBytesInput) returns (output: Result<seq<uint8>, Error>)
      ensures GenerateRandomBytesCalledWith(input)
      ensures output.Success? ==> GenerateRandomBytesSucceededWith(input, output.value)
      decreases input

    method Digest(input: DigestInput) returns (output: Result<seq<uint8>, Error>)
      ensures DigestCalledWith(input)
      ensures output.Success? ==> DigestSucceededWith(input, output.value)
      decreases input

    method HMac(input: HMacInput) returns (output: Result<seq<uint8>, Error>)
      ensures HMacCalledWith(input)
      ensures output.Success? ==> HMacSucceededWith(input, output.value)
      decreases input

    method HkdfExtract(input: HkdfExtractInput) returns (output: Result<seq<uint8>, Error>)
      ensures HkdfExtractCalledWith(input)
      ensures output.Success? ==> HkdfExtractSucceededWith(input, output.value)
      decreases input

    method HkdfExpand(input: HkdfExpandInput) returns (output: Result<seq<uint8>, Error>)
      ensures HkdfExpandCalledWith(input)
      ensures output.Success? ==> HkdfExpandSucceededWith(input, output.value)
      decreases input

    method Hkdf(input: HkdfInput) returns (output: Result<seq<uint8>, Error>)
      ensures HkdfCalledWith(input)
      ensures output.Success? ==> HkdfSucceededWith(input, output.value)
      decreases input

    method AESEncrypt(input: AESEncryptInput) returns (output: Result<AESEncryptOutput, Error>)
      ensures AESEncryptCalledWith(input)
      ensures output.Success? ==> AESEncryptSucceededWith(input, output.value)
      decreases input

    method AESDecrypt(input: AESDecryptInput) returns (output: Result<seq<uint8>, Error>)
      ensures AESDecryptCalledWith(input)
      ensures output.Success? ==> AESDecryptSucceededWith(input, output.value)
      decreases input
  }

  datatype CryptoConfig = CryptoConfig

  datatype DigestAlgorithm = SHA_512 | SHA_384 | SHA_256

  datatype DigestInput = DigestInput(nameonly digestAlgorithm: DigestAlgorithm, nameonly message: seq<uint8>)

  datatype GenerateRandomBytesInput = GenerateRandomBytesInput(nameonly length: PositiveInteger)

  datatype HkdfExpandInput = HkdfExpandInput(nameonly digestAlgorithm: DigestAlgorithm, nameonly prk: seq<uint8>, nameonly info: seq<uint8>, nameonly expectedLength: PositiveInteger)

  datatype HkdfExtractInput = HkdfExtractInput(nameonly digestAlgorithm: DigestAlgorithm, nameonly salt: Option<seq<uint8>>, nameonly ikm: seq<uint8>)

  datatype HkdfInput = HkdfInput(nameonly digestAlgorithm: DigestAlgorithm, nameonly salt: Option<seq<uint8>>, nameonly ikm: seq<uint8>, nameonly info: seq<uint8>, nameonly expectedLength: PositiveInteger)

  datatype HMacInput = HMacInput(nameonly digestAlgorithm: DigestAlgorithm, nameonly key: seq<uint8>, nameonly message: seq<uint8>)

  type PositiveInteger = x: int32
    | IsValid_PositiveInteger(x)
    witness *

  datatype Error = AwsCryptographicPrimitivesError(nameonly message: string) | Opaque(obj: object)

  type OpaqueError = e: Error
    | e.Opaque?
    witness *

  predicate {:axiom} GenerateRandomBytesCalledWith(input: GenerateRandomBytesInput)
    decreases input

  lemma {:axiom} AssumeGenerateRandomBytesCalledWith(input: GenerateRandomBytesInput)
    ensures GenerateRandomBytesCalledWith(input)
    decreases input

  predicate {:axiom} GenerateRandomBytesSucceededWith(input: GenerateRandomBytesInput, output: seq<uint8>)
    decreases input, output

  lemma {:axiom} AssumeGenerateRandomBytesSucceededWith(input: GenerateRandomBytesInput, output: seq<uint8>)
    ensures GenerateRandomBytesSucceededWith(input, output)
    decreases input, output

  predicate {:axiom} DigestCalledWith(input: DigestInput)
    decreases input

  lemma {:axiom} AssumeDigestCalledWith(input: DigestInput)
    ensures DigestCalledWith(input)
    decreases input

  predicate {:axiom} DigestSucceededWith(input: DigestInput, output: seq<uint8>)
    decreases input, output

  lemma {:axiom} AssumeDigestSucceededWith(input: DigestInput, output: seq<uint8>)
    ensures DigestSucceededWith(input, output)
    decreases input, output

  predicate {:axiom} HMacCalledWith(input: HMacInput)
    decreases input

  lemma {:axiom} AssumeHMacCalledWith(input: HMacInput)
    ensures HMacCalledWith(input)
    decreases input

  predicate {:axiom} HMacSucceededWith(input: HMacInput, output: seq<uint8>)
    decreases input, output

  lemma {:axiom} AssumeHMacSucceededWith(input: HMacInput, output: seq<uint8>)
    ensures HMacSucceededWith(input, output)
    decreases input, output

  predicate {:axiom} HkdfExtractCalledWith(input: HkdfExtractInput)
    decreases input

  lemma {:axiom} AssumeHkdfExtractCalledWith(input: HkdfExtractInput)
    ensures HkdfExtractCalledWith(input)
    decreases input

  predicate {:axiom} HkdfExtractSucceededWith(input: HkdfExtractInput, output: seq<uint8>)
    decreases input, output

  lemma {:axiom} AssumeHkdfExtractSucceededWith(input: HkdfExtractInput, output: seq<uint8>)
    ensures HkdfExtractSucceededWith(input, output)
    decreases input, output

  predicate {:axiom} HkdfExpandCalledWith(input: HkdfExpandInput)
    decreases input

  lemma {:axiom} AssumeHkdfExpandCalledWith(input: HkdfExpandInput)
    ensures HkdfExpandCalledWith(input)
    decreases input

  predicate {:axiom} HkdfExpandSucceededWith(input: HkdfExpandInput, output: seq<uint8>)
    decreases input, output

  lemma {:axiom} AssumeHkdfExpandSucceededWith(input: HkdfExpandInput, output: seq<uint8>)
    ensures HkdfExpandSucceededWith(input, output)
    decreases input, output

  predicate {:axiom} HkdfCalledWith(input: HkdfInput)
    decreases input

  lemma {:axiom} AssumeHkdfCalledWith(input: HkdfInput)
    ensures HkdfCalledWith(input)
    decreases input

  predicate {:axiom} HkdfSucceededWith(input: HkdfInput, output: seq<uint8>)
    decreases input, output

  lemma {:axiom} AssumeHkdfSucceededWith(input: HkdfInput, output: seq<uint8>)
    ensures HkdfSucceededWith(input, output)
    decreases input, output

  predicate {:axiom} AESEncryptCalledWith(input: AESEncryptInput)
    decreases input

  lemma {:axiom} AssumeAESEncryptCalledWith(input: AESEncryptInput)
    ensures AESEncryptCalledWith(input)
    decreases input

  predicate {:axiom} AESEncryptSucceededWith(input: AESEncryptInput, output: AESEncryptOutput)
    decreases input, output

  lemma {:axiom} AssumeAESEncryptSucceededWith(input: AESEncryptInput, output: AESEncryptOutput)
    ensures AESEncryptSucceededWith(input, output)
    decreases input, output

  predicate {:axiom} AESDecryptCalledWith(input: AESDecryptInput)
    decreases input

  lemma {:axiom} AssumeAESDecryptCalledWith(input: AESDecryptInput)
    ensures AESDecryptCalledWith(input)
    decreases input

  predicate {:axiom} AESDecryptSucceededWith(input: AESDecryptInput, output: seq<uint8>)
    decreases input, output

  lemma {:axiom} AssumeAESDecryptSucceededWith(input: AESDecryptInput, output: seq<uint8>)
    ensures AESDecryptSucceededWith(input, output)
    decreases input, output

  predicate method IsValid_PositiveInteger(x: int32)
    decreases x
  {
    0 <= x
  }
}

abstract module AwsCryptographyPrimitivesAbstract {

  import opened Wrappers

  import opened UInt = StandardLibrary.UInt

  import opened UTF8

  import opened Types = AwsCryptographyPrimitivesTypes
  function method DefaultCryptoConfig(): CryptoConfig

  method Crypto(config: CryptoConfig := DefaultCryptoConfig()) returns (res: Result<IAwsCryptographicPrimitivesClient, Error>)
    decreases config
}

module StandardLibrary {

  import opened Wrappers

  import opened U = UInt
  lemma SeqTakeAppend<A>(s: seq<A>, i: int)
    requires 0 <= i < |s|
    ensures s[..i] + [s[i]] == s[..i + 1]
    decreases s, i
  {
  }

  function method {:tailrecursion} Join<T>(ss: seq<seq<T>>, joiner: seq<T>): (s: seq<T>)
    requires 0 < |ss|
    decreases ss, joiner
  {
    if |ss| == 1 then
      ss[0]
    else
      ss[0] + joiner + Join(ss[1..], joiner)
  }

  function method {:tailrecursion} Split<T(==)>(s: seq<T>, delim: T): (res: seq<seq<T>>)
    ensures delim !in s ==> res == [s]
    ensures s == [] ==> res == [[]]
    ensures 0 < |res|
    ensures forall i: int :: 0 <= i < |res| ==> delim !in res[i]
    ensures Join(res, [delim]) == s
    decreases |s|
  {
    var i: Option<nat> := FindIndexMatching(s, delim, 0);
    if i.Some? then
      [s[..i.value]] + Split(s[i.value + 1..], delim)
    else
      [s]
  }

  lemma /*{:_induction s}*/ WillSplitOnDelim<T>(s: seq<T>, delim: T, prefix: seq<T>)
    requires |prefix| < |s|
    requires forall i: int :: 0 <= i < |prefix| ==> prefix[i] == s[i]
    requires delim !in prefix && s[|prefix|] == delim
    ensures Split(s, delim) == [prefix] + Split(s[|prefix| + 1..], delim)
    decreases s, prefix
  {
  }

  lemma /*{:_induction s}*/ WillNotSplitWithOutDelim<T>(s: seq<T>, delim: T)
    requires delim !in s
    ensures Split(s, delim) == [s]
    decreases s
  {
  }

  lemma FindIndexMatchingLocatesElem<T>(s: seq<T>, c: T, start: nat, elemIndex: nat)
    requires start <= elemIndex <= |s|
    requires forall i: int :: start <= i < elemIndex ==> s[i] != c
    requires elemIndex == |s| || s[elemIndex] == c
    ensures FindIndexMatching(s, c, start) == if elemIndex == |s| then None else Some(elemIndex)
    decreases elemIndex - start
  {
  }

  function method FindIndexMatching<T(==)>(s: seq<T>, c: T, i: nat): (index: Option<nat>)
    requires i <= |s|
    ensures index.Some? ==> i <= index.value < |s| && s[index.value] == c && c !in s[i .. index.value]
    ensures index.None? ==> c !in s[i..]
    decreases |s| - i
  {
    FindIndex(s, (x: T) => x == c, i)
  }

  function method {:tailrecursion} FindIndex<T>(s: seq<T>, f: T -> bool, i: nat): (index: Option<nat>)
    requires i <= |s|
    ensures index.Some? ==> i <= index.value < |s| && f(s[index.value]) && forall j: int :: i <= j < index.value ==> !f(s[j])
    ensures index.None? ==> forall j: int :: i <= j < |s| ==> !f(s[j])
    decreases |s| - i
  {
    if i == |s| then
      None
    else if f(s[i]) then
      Some(i)
    else
      FindIndex(s, f, i + 1)
  }

  function method {:tailrecursion} Filter<T>(s: seq<T>, f: T -> bool): (res: seq<T>)
    ensures forall i: int :: 0 <= i < |s| && f(s[i]) ==> s[i] in res
    ensures forall i: int :: 0 <= i < |res| ==> res[i] in s && f(res[i])
    ensures |res| <= |s|
    decreases s
  {
    if |s| == 0 then
      []
    else if f(s[0]) then
      [s[0]] + Filter(s[1..], f)
    else
      Filter(s[1..], f)
  }

  lemma /*{:_induction s, s', f}*/ FilterIsDistributive<T>(s: seq<T>, s': seq<T>, f: T -> bool)
    ensures Filter(s + s', f) == Filter(s, f) + Filter(s', f)
    decreases s, s'
  {
  }

  function method Min(a: int, b: int): int
    decreases a, b
  {
    if a < b then
      a
    else
      b
  }

  function method Fill<T>(value: T, n: nat): seq<T>
    ensures |Fill(value, n)| == n
    ensures forall i: int :: 0 <= i < n ==> Fill(value, n)[i] == value
    decreases n
  {
    seq(n, (_: int) => value)
  }

  method SeqToArray<T>(s: seq<T>) returns (a: array<T>)
    ensures fresh(a)
    ensures a.Length == |s|
    ensures forall i: int :: 0 <= i < |s| ==> a[i] == s[i]
    decreases s
  {
    a := new T[|s|] ((i: int) requires 0 <= i < |s| => s[i]);
  }

  lemma SeqPartsMakeWhole<T>(s: seq<T>, i: nat)
    requires 0 <= i <= |s|
    ensures s[..i] + s[i..] == s
    decreases s, i
  {
  }

  predicate method LexicographicLessOrEqual<T(==)>(a: seq<T>, b: seq<T>, less: (T, T) -> bool)
    decreases a, b
  {
    exists k: int :: 
      0 <= k <= |a| &&
      LexicographicLessOrEqualAux(a, b, less, k)
  }

  predicate method LexicographicLessOrEqualAux<T(==)>(a: seq<T>, b: seq<T>, less: (T, T) -> bool, lengthOfCommonPrefix: nat)
    requires 0 <= lengthOfCommonPrefix <= |a|
    decreases a, b, lengthOfCommonPrefix
  {
    lengthOfCommonPrefix <= |b| &&
    (forall i: int :: 
      0 <= i < lengthOfCommonPrefix ==>
        a[i] == b[i]) &&
    (lengthOfCommonPrefix == |a| || (lengthOfCommonPrefix < |b| && less(a[lengthOfCommonPrefix], b[lengthOfCommonPrefix])))
  }

  predicate Trichotomous<T(!new)>(less: (T, T) -> bool)
  {
    (forall x: T, y: T :: 
      less(x, y) || x == y || less(y, x)) &&
    (forall x: T, y: T :: 
      less(x, y) &&
      less(y, x) ==>
        false) &&
    forall x: T, y: T :: 
      less(x, y) ==>
        x != y
  }

  predicate Transitive<T(!new)>(R: (T, T) -> bool)
  {
    forall x: T, y: T, z: T :: 
      R(x, y) &&
      R(y, z) ==>
        R(x, z)
  }

  lemma UInt8LessIsTrichotomousTransitive()
    ensures Trichotomous(UInt8Less)
    ensures Transitive(UInt8Less)
  {
  }

  lemma LexIsReflexive<T>(a: seq<T>, less: (T, T) -> bool)
    ensures LexicographicLessOrEqual(a, a, less)
    decreases a
  {
  }

  lemma LexIsAntisymmetric<T>(a: seq<T>, b: seq<T>, less: (T, T) -> bool)
    requires Trich: Trichotomous(less)
    requires LexicographicLessOrEqual(a, b, less)
    requires LexicographicLessOrEqual(b, a, less)
    ensures a == b
    decreases a, b
  {
  }

  lemma LexIsTransitive<T>(a: seq<T>, b: seq<T>, c: seq<T>, less: (T, T) -> bool)
    requires Transitive(less)
    requires LexicographicLessOrEqual(a, b, less)
    requires LexicographicLessOrEqual(b, c, less)
    ensures LexicographicLessOrEqual(a, c, less)
    decreases a, b, c
  {
  }

  lemma LexIsTotal<T>(a: seq<T>, b: seq<T>, less: (T, T) -> bool)
    requires Trich: Trichotomous(less)
    ensures LexicographicLessOrEqual(a, b, less) || LexicographicLessOrEqual(b, a, less)
    decreases a, b
  {
  }

  function method {:tailrecursion} SetToOrderedSequence<T(==,!new)>(s: set<seq<T>>, less: (T, T) -> bool): (q: seq<seq<T>>)
    requires Trichotomous(less) && Transitive(less)
    ensures |s| == |q|
    ensures forall i: int :: 0 <= i < |q| ==> q[i] in s
    ensures forall k: seq<T> :: k in s ==> k in q
    ensures forall i: int :: 0 < i < |q| ==> LexicographicLessOrEqual(q[i - 1], q[i], less)
    ensures forall i: int, j: int | 0 <= i < j < |q| :: q[i] != q[j]
    decreases s
  {
    if s == {} then
      []
    else
      ThereIsAMinimum(s, less); assert forall a: seq<T>, b: seq<T> :: IsMinimum(a, s, less) && IsMinimum(b, s, less) ==> a == b by {
    forall a: seq<T>, b: seq<T> | IsMinimum(a, s, less) && IsMinimum(b, s, less) {
      MinimumIsUnique(a, b, s, less);
    }
  } var a: seq<T> :| a in s && IsMinimum(a, s, less); [a] + SetToOrderedSequence(s - {a}, less)
  }

  predicate method IsMinimum<T(==)>(a: seq<T>, s: set<seq<T>>, less: (T, T) -> bool)
    decreases a, s
  {
    a in s &&
    forall z: seq<T> :: 
      z in s ==>
        LexicographicLessOrEqual(a, z, less)
  }

  lemma ThereIsAMinimum<T>(s: set<seq<T>>, less: (T, T) -> bool)
    requires s != {}
    requires Trichotomous(less) && Transitive(less)
    ensures exists a: seq<T> :: IsMinimum(a, s, less)
    decreases s
  {
  }

  lemma MinimumIsUnique<T>(a: seq<T>, b: seq<T>, s: set<seq<T>>, less: (T, T) -> bool)
    requires IsMinimum(a, s, less) && IsMinimum(b, s, less)
    requires Trichotomous(less)
    ensures a == b
    decreases a, b, s
  {
  }

  lemma FindMinimum<T>(s: set<seq<T>>, less: (T, T) -> bool) returns (a: seq<T>)
    requires s != {}
    requires Trichotomous(less) && Transitive(less)
    ensures IsMinimum(a, s, less)
    decreases s
  {
  }

  module UInt {
    newtype uint8 = x: int
      | 0 <= x < 256

    newtype uint16 = x: int
      | 0 <= x < 65536

    newtype uint32 = x: int
      | 0 <= x < 4294967296

    newtype uint64 = x: int
      | 0 <= x < 18446744073709551616

    newtype int32 = x: int
      | -2147483648 <= x < 2147483648

    newtype int64 = x: int
      | -9223372036854775808 <= x < 9223372036854775808

    newtype posInt64 = x: int
      | 0 < x < 9223372036854775808
      witness 1

    type seq16<T> = s: seq<T>
      | HasUint16Len(s)

    type Uint8Seq16 = seq16<uint8>

    type seq32<T> = s: seq<T>
      | HasUint32Len(s)

    type Uint8Seq32 = seq32<uint8>

    type seq64<T> = s: seq<T>
      | HasUint64Len(s)

    type Uint8Seq64 = seq64<uint8>

    const UINT16_LIMIT := 65536
    const UINT32_LIMIT := 4294967296
    const UINT64_LIMIT := 18446744073709551616
    const INT32_MAX_LIMIT := 2147483648
    const INT64_MAX_LIMIT := 9223372036854775808

    predicate method UInt8Less(a: uint8, b: uint8)
      decreases a, b
    {
      a < b
    }

    predicate method HasUint16Len<T>(s: seq<T>)
      decreases s
    {
      |s| < UINT16_LIMIT
    }

    predicate method HasUint32Len<T>(s: seq<T>)
      decreases s
    {
      |s| < UINT32_LIMIT
    }

    predicate method HasUint64Len<T>(s: seq<T>)
      decreases s
    {
      |s| < UINT64_LIMIT
    }

    function method UInt16ToSeq(x: uint16): (ret: seq<uint8>)
      ensures |ret| == 2
      ensures 256 * ret[0] as uint16 + ret[1] as uint16 == x
      decreases x
    {
      var b0: uint8 := (x / 256) as uint8;
      var b1: uint8 := (x % 256) as uint8;
      [b0, b1]
    }

    function method SeqToUInt16(s: seq<uint8>): (x: uint16)
      requires |s| == 2
      ensures UInt16ToSeq(x) == s
      ensures x >= 0
      decreases s
    {
      var x0: uint16 := s[0] as uint16 * 256;
      x0 + s[1] as uint16
    }

    lemma UInt16SeqSerializeDeserialize(x: uint16)
      ensures SeqToUInt16(UInt16ToSeq(x)) == x
      decreases x
    {
    }

    lemma UInt16SeqDeserializeSerialize(s: seq<uint8>)
      requires |s| == 2
      ensures UInt16ToSeq(SeqToUInt16(s)) == s
      decreases s
    {
    }

    function method UInt32ToSeq(x: uint32): (ret: seq<uint8>)
      ensures |ret| == 4
      ensures 16777216 * ret[0] as uint32 + 65536 * ret[1] as uint32 + 256 * ret[2] as uint32 + ret[3] as uint32 == x
      decreases x
    {
      var b0: uint8 := (x / 16777216) as uint8;
      var x0: uint32 := x - b0 as uint32 * 16777216;
      var b1: uint8 := (x0 / 65536) as uint8;
      var x1: uint32 := x0 - b1 as uint32 * 65536;
      var b2: uint8 := (x1 / 256) as uint8;
      var b3: uint8 := (x1 % 256) as uint8;
      [b0, b1, b2, b3]
    }

    function method SeqToUInt32(s: seq<uint8>): (x: uint32)
      requires |s| == 4
      ensures UInt32ToSeq(x) == s
      decreases s
    {
      var x0: uint32 := s[0] as uint32 * 16777216;
      var x1: uint32 := x0 + s[1] as uint32 * 65536;
      var x2: uint32 := x1 + s[2] as uint32 * 256;
      x2 + s[3] as uint32
    }

    lemma UInt32SeqSerializeDeserialize(x: uint32)
      ensures SeqToUInt32(UInt32ToSeq(x)) == x
      decreases x
    {
    }

    lemma UInt32SeqDeserializeSerialize(s: seq<uint8>)
      requires |s| == 4
      ensures UInt32ToSeq(SeqToUInt32(s)) == s
      decreases s
    {
    }

    function method UInt64ToSeq(x: uint64): (ret: seq<uint8>)
      ensures |ret| == 8
      ensures 72057594037927936 * ret[0] as uint64 + 281474976710656 * ret[1] as uint64 + 1099511627776 * ret[2] as uint64 + 4294967296 * ret[3] as uint64 + 16777216 * ret[4] as uint64 + 65536 * ret[5] as uint64 + 256 * ret[6] as uint64 + ret[7] as uint64 == x
      decreases x
    {
      var b0: uint8 := (x / 72057594037927936) as uint8;
      var x0: uint64 := x - b0 as uint64 * 72057594037927936;
      var b1: uint8 := (x0 / 281474976710656) as uint8;
      var x1: uint64 := x0 - b1 as uint64 * 281474976710656;
      var b2: uint8 := (x1 / 1099511627776) as uint8;
      var x2: uint64 := x1 - b2 as uint64 * 1099511627776;
      var b3: uint8 := (x2 / 4294967296) as uint8;
      var x3: uint64 := x2 - b3 as uint64 * 4294967296;
      var b4: uint8 := (x3 / 16777216) as uint8;
      var x4: uint64 := x3 - b4 as uint64 * 16777216;
      var b5: uint8 := (x4 / 65536) as uint8;
      var x5: uint64 := x4 - b5 as uint64 * 65536;
      var b6: uint8 := (x5 / 256) as uint8;
      var b7: uint8 := (x5 % 256) as uint8;
      [b0, b1, b2, b3, b4, b5, b6, b7]
    }

    function method SeqToUInt64(s: seq<uint8>): (x: uint64)
      requires |s| == 8
      ensures UInt64ToSeq(x) == s
      decreases s
    {
      var x0: uint64 := s[0] as uint64 * 72057594037927936;
      var x1: uint64 := x0 + s[1] as uint64 * 281474976710656;
      var x2: uint64 := x1 + s[2] as uint64 * 1099511627776;
      var x3: uint64 := x2 + s[3] as uint64 * 4294967296;
      var x4: uint64 := x3 + s[4] as uint64 * 16777216;
      var x5: uint64 := x4 + s[5] as uint64 * 65536;
      var x6: uint64 := x5 + s[6] as uint64 * 256;
      var x: uint64 := x6 + s[7] as uint64;
      UInt64SeqSerialize(x, s);
      x
    }

    lemma UInt64SeqSerialize(x: uint64, s: seq<uint8>)
      requires |s| == 8
      requires 72057594037927936 * s[0] as uint64 + 281474976710656 * s[1] as uint64 + 1099511627776 * s[2] as uint64 + 4294967296 * s[3] as uint64 + 16777216 * s[4] as uint64 + 65536 * s[5] as uint64 + 256 * s[6] as uint64 + s[7] as uint64 == x
      ensures UInt64ToSeq(x) == s
      decreases x, s
    {
    }

    lemma UInt64SeqSerializeDeserialize(x: uint64)
      ensures SeqToUInt64(UInt64ToSeq(x)) == x
      decreases x
    {
    }

    lemma UInt64SeqDeserializeSerialize(s: seq<uint8>)
      requires |s| == 8
      ensures UInt64ToSeq(SeqToUInt64(s)) == s
      decreases s
    {
    }

    function SeqToNat(s: seq<uint8>): nat
      decreases s
    {
      if s == [] then
        0
      else
        ghost var finalIndex: int := |s| - 1; SeqToNat(s[..finalIndex]) * 256 + s[finalIndex] as nat
    }

    lemma /*{:_induction s}*/ SeqToNatZeroPrefix(s: seq<uint8>)
      ensures SeqToNat(s) == SeqToNat([0] + s)
      decreases s
    {
    }

    lemma /*{:_induction s}*/ SeqWithUInt32Suffix(s: seq<uint8>, n: nat)
      requires n < UINT32_LIMIT
      requires 4 <= |s|
      requires ghost var suffixStartIndex: int := |s| - 4; s[suffixStartIndex..] == UInt32ToSeq(n as uint32) && forall i: int :: 0 <= i < suffixStartIndex ==> s[i] == 0
      ensures SeqToNat(s) == n
      decreases s, n
    {
    }
  }
}

module {:extern ""UTF8""} UTF8 {

  import opened Wrappers

  import opened UInt = StandardLibrary.UInt
  type ValidUTF8Bytes = i: seq<uint8>
    | ValidUTF8Seq(i)
    witness []

  function method {:extern ""Encode""} Encode(s: string): (res: Result<ValidUTF8Bytes, string>)
    ensures IsASCIIString(s) ==> res.Success? && |res.value| == |s|
    decreases s

  function method {:extern ""Decode""} Decode(b: ValidUTF8Bytes): (res: Result<string, string>)
    decreases b

  predicate method IsASCIIString(s: string)
    decreases s
  {
    forall i: int :: 
      0 <= i < |s| ==>
        s[i] as int < 128
  }

  predicate method Uses1Byte(s: seq<uint8>)
    requires |s| >= 1
    decreases s
  {
    0 <= s[0] <= 127
  }

  predicate method Uses2Bytes(s: seq<uint8>)
    requires |s| >= 2
    decreases s
  {
    194 <= s[0] <= 223 &&
    128 <= s[1] <= 191
  }

  predicate method Uses3Bytes(s: seq<uint8>)
    requires |s| >= 3
    decreases s
  {
    (s[0] == 224 && 160 <= s[1] <= 191 && 128 <= s[2] <= 191) || (225 <= s[0] <= 236 && 128 <= s[1] <= 191 && 128 <= s[2] <= 191) || (s[0] == 237 && 128 <= s[1] <= 159 && 128 <= s[2] <= 191) || (238 <= s[0] <= 239 && 128 <= s[1] <= 191 && 128 <= s[2] <= 191)
  }

  predicate method Uses4Bytes(s: seq<uint8>)
    requires |s| >= 4
    decreases s
  {
    (s[0] == 240 && 144 <= s[1] <= 191 && 128 <= s[2] <= 191 && 128 <= s[3] <= 191) || (241 <= s[0] <= 243 && 128 <= s[1] <= 191 && 128 <= s[2] <= 191 && 128 <= s[3] <= 191) || (s[0] == 244 && 128 <= s[1] <= 143 && 128 <= s[2] <= 191 && 128 <= s[3] <= 191)
  }

  predicate method {:tailrecursion} ValidUTF8Range(a: seq<uint8>, lo: nat, hi: nat)
    requires lo <= hi <= |a|
    decreases hi - lo
  {
    if lo == hi then
      true
    else
      var r: seq<uint8> := a[lo .. hi]; if Uses1Byte(r) then ValidUTF8Range(a, lo + 1, hi) else if 2 <= |r| && Uses2Bytes(r) then ValidUTF8Range(a, lo + 2, hi) else if 3 <= |r| && Uses3Bytes(r) then ValidUTF8Range(a, lo + 3, hi) else if 4 <= |r| && Uses4Bytes(r) then ValidUTF8Range(a, lo + 4, hi) else false
  }

  lemma /*{:_induction a, b, c, lo, hi}*/ ValidUTF8Embed(a: seq<uint8>, b: seq<uint8>, c: seq<uint8>, lo: nat, hi: nat)
    requires lo <= hi <= |b|
    ensures ValidUTF8Range(b, lo, hi) == ValidUTF8Range(a + b + c, |a| + lo, |a| + hi)
    decreases hi - lo
  {
  }

  predicate method ValidUTF8Seq(s: seq<uint8>)
    decreases s
  {
    ValidUTF8Range(s, 0, |s|)
  }

  lemma ValidUTF8Concat(s: seq<uint8>, t: seq<uint8>)
    requires ValidUTF8Seq(s) && ValidUTF8Seq(t)
    ensures ValidUTF8Seq(s + t)
    decreases s, t
  {
  }
}

module Wrappers {
  datatype Option<+T> = None | Some(value: T) {
    function method ToResult(): Result<T, string>
      decreases this
    {
      match this
      case Some(v) =>
        Success(v)
      case None() =>
        Failure(""Option is None"")
    }

    function method UnwrapOr(default: T): T
      decreases this
    {
      match this
      case Some(v) =>
        v
      case None() =>
        default
    }

    predicate method IsFailure()
      decreases this
    {
      None?
    }

    function method PropagateFailure<U>(): Option<U>
      requires None?
      decreases this
    {
      None
    }

    function method Extract(): T
      requires Some?
      decreases this
    {
      value
    }
  }

  datatype Result<+T, +R> = Success(value: T) | Failure(error: R) {
    function method ToOption(): Option<T>
      decreases this
    {
      match this
      case Success(s) =>
        Some(s)
      case Failure(e) =>
        None()
    }

    function method UnwrapOr(default: T): T
      decreases this
    {
      match this
      case Success(s) =>
        s
      case Failure(e) =>
        default
    }

    predicate method IsFailure()
      decreases this
    {
      Failure?
    }

    function method PropagateFailure<U>(): Result<U, R>
      requires Failure?
      decreases this
    {
      Failure(this.error)
    }

    function method MapFailure<NewR>(reWrap: R -> NewR): Result<T, NewR>
      decreases this
    {
      match this
      case Success(s) =>
        Success(s)
      case Failure(e) =>
        Failure(reWrap(e))
    }

    function method Extract(): T
      requires Success?
      decreases this
    {
      value
    }
  }

  datatype Outcome<E> = Pass | Fail(error: E) {
    predicate method IsFailure()
      decreases this
    {
      Fail?
    }

    function method PropagateFailure<U>(): Result<U, E>
      requires Fail?
      decreases this
    {
      Failure(this.error)
    }
  }

  function method Need<E>(condition: bool, error: E): (result: Outcome<E>)
    decreases condition
  {
    if condition then
      Pass
    else
      Fail(error)
  }
}

module Aws {

  module Cryptography {

    module {:extern ""Dafny.Aws.Cryptography.Primitives""} Primitives refines AwsCryptographyPrimitivesAbstract {

      import Random

      import AESEncryption

      import D = Digest

      import WrappedHMAC

      import WrappedHKDF
      class AtomicPrimitivesClient extends IAwsCryptographicPrimitivesClient {
        const config: CryptoConfig

        constructor (config: CryptoConfig)
          decreases config
        {
          this.config := config;
        }

        method GenerateRandomBytes(input: GenerateRandomBytesInput) returns (output: Result<seq<uint8>, Error>)
          ensures GenerateRandomBytesCalledWith(input)
          ensures output.Success? ==> GenerateRandomBytesSucceededWith(input, output.value)
          decreases input
        {
          AssumeGenerateRandomBytesCalledWith(input);
          var value :- Random.GenerateBytes(input.length);
          AssumeGenerateRandomBytesSucceededWith(input, value);
          output := Success(value);
        }

        method Digest(input: DigestInput) returns (output: Result<seq<uint8>, Error>)
          ensures DigestCalledWith(input)
          ensures output.Success? ==> DigestSucceededWith(input, output.value)
          decreases input
        {
          AssumeDigestCalledWith(input);
          var value :- D.Digest(input);
          AssumeDigestSucceededWith(input, value);
          output := Success(value);
        }

        method HMac(input: HMacInput) returns (output: Result<seq<uint8>, Error>)
          ensures HMacCalledWith(input)
          ensures output.Success? ==> HMacSucceededWith(input, output.value)
          decreases input
        {
          AssumeHMacCalledWith(input);
          var value :- WrappedHMAC.Digest(input);
          AssumeHMacSucceededWith(input, value);
          output := Success(value);
        }

        method HkdfExtract(input: HkdfExtractInput) returns (output: Result<seq<uint8>, Error>)
          ensures HkdfExtractCalledWith(input)
          ensures output.Success? ==> HkdfExtractSucceededWith(input, output.value)
          decreases input
        {
          AssumeHkdfExtractCalledWith(input);
          :- Need((input.salt.None? || |input.salt.value| != 0) && |input.ikm| < INT32_MAX_LIMIT, Types.AwsCryptographicPrimitivesError(message := ""No.""));
          var value := WrappedHKDF.Extract(input);
          AssumeHkdfExtractSucceededWith(input, value);
          output := Success(value);
        }

        method HkdfExpand(input: HkdfExpandInput) returns (output: Result<seq<uint8>, Error>)
          ensures HkdfExpandCalledWith(input)
          ensures output.Success? ==> HkdfExpandSucceededWith(input, output.value)
          decreases input
        {
          AssumeHkdfExpandCalledWith(input);
          :- Need(1 <= input.expectedLength as int <= 255 * D.Length(input.digestAlgorithm) && |input.info| < INT32_MAX_LIMIT && D.Length(input.digestAlgorithm) == |input.prk|, Types.AwsCryptographicPrimitivesError(message := ""No.""));
          var value := WrappedHKDF.Expand(input);
          AssumeHkdfExpandSucceededWith(input, value);
          output := Success(value);
        }

        method Hkdf(input: HkdfInput) returns (output: Result<seq<uint8>, Error>)
          ensures HkdfCalledWith(input)
          ensures output.Success? ==> HkdfSucceededWith(input, output.value)
          decreases input
        {
          AssumeHkdfCalledWith(input);
          :- Need(0 <= input.expectedLength as int <= 255 * D.Length(input.digestAlgorithm) && (input.salt.None? || |input.salt.value| != 0) && |input.info| < INT32_MAX_LIMIT && |input.ikm| < INT32_MAX_LIMIT, Types.AwsCryptographicPrimitivesError(message := ""No.""));
          var value := WrappedHKDF.Hkdf(input);
          AssumeHkdfSucceededWith(input, value);
          output := Success(value);
        }

        method AESDecrypt(input: AESDecryptInput) returns (output: Result<seq<uint8>, Error>)
          ensures AESDecryptCalledWith(input)
          ensures output.Success? ==> AESDecryptSucceededWith(input, output.value)
          decreases input
        {
          AssumeAESDecryptCalledWith(input);
          :- Need(|input.key| == input.encAlg.keyLength as int && |input.iv| == input.encAlg.ivLength as int && |input.authTag| == input.encAlg.tagLength as int, Types.AwsCryptographicPrimitivesError(message := ""Request does not match algorithm.""));
          var value :- AESEncryption.AESDecrypt(input);
          AssumeAESDecryptSucceededWith(input, value);
          output := Success(value);
        }

        method AESEncrypt(input: AESEncryptInput) returns (output: Result<AESEncryptOutput, Error>)
          ensures AESEncryptCalledWith(input)
          ensures output.Success? ==> AESEncryptSucceededWith(input, output.value)
          ensures output.Success? ==> AESEncryption.EncryptionOutputEncryptedWithAAD(output.value, input.aad)
          decreases input
        {
          AssumeAESEncryptCalledWith(input);
          :- Need(|input.iv| == input.encAlg.ivLength as int && |input.key| == input.encAlg.keyLength as int, Types.AwsCryptographicPrimitivesError(message := ""Request does not match algorithm.""));
          var value :- AESEncryption.AESEncrypt(input);
          AssumeAESEncryptSucceededWith(input, value);
          output := Success(value);
        }
      }

      function method DefaultCryptoConfig(): CryptoConfig
      {
        CryptoConfig()
      }

      method Crypto(config: CryptoConfig := DefaultCryptoConfig()) returns (res: Result<IAwsCryptographicPrimitivesClient, Error>)
        decreases config
      {
        var client := new AtomicPrimitivesClient(config);
        return Success(client);
      }

      import opened Wrappers

      import opened UInt = StandardLibrary.UInt

      import opened UTF8

      import opened Types = AwsCryptographyPrimitivesTypes
    }
  }
}
")]

//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

#if ISDAFNYRUNTIMELIB
using System; // for Func
using System.Numerics;
#endif

namespace DafnyAssembly {
  [AttributeUsage(AttributeTargets.Assembly)]
  public class DafnySourceAttribute : Attribute {
    public readonly string dafnySourceText;
    public DafnySourceAttribute(string txt) { dafnySourceText = txt; }
  }
}

namespace Dafny {
  using System.Collections.Generic;
  using System.Collections.Immutable;
  using System.Linq;

  public interface ISet<out T> {
    int Count { get; }
    long LongCount { get; }
    IEnumerable<T> Elements { get; }
    IEnumerable<ISet<T>> AllSubsets { get; }
    bool Contains<G>(G t);
    bool EqualsAux(ISet<object> other);
    ISet<U> DowncastClone<U>(Func<T, U> converter);
  }

  public class Set<T> : ISet<T> {
    readonly ImmutableHashSet<T> setImpl;
    readonly bool containsNull;
    Set(ImmutableHashSet<T> d, bool containsNull) {
      this.setImpl = d;
      this.containsNull = containsNull;
    }

    public static readonly ISet<T> Empty = new Set<T>(ImmutableHashSet<T>.Empty, false);

    private static readonly TypeDescriptor<ISet<T>> _TYPE = new Dafny.TypeDescriptor<ISet<T>>(Empty);
    public static TypeDescriptor<ISet<T>> _TypeDescriptor() {
      return _TYPE;
    }

    public static ISet<T> FromElements(params T[] values) {
      return FromCollection(values);
    }

    public static Set<T> FromISet(ISet<T> s) {
      return s as Set<T> ?? FromCollection(s.Elements);
    }

    public static Set<T> FromCollection(IEnumerable<T> values) {
      var d = ImmutableHashSet<T>.Empty.ToBuilder();
      var containsNull = false;
      foreach (T t in values) {
        if (t == null) {
          containsNull = true;
        } else {
          d.Add(t);
        }
      }

      return new Set<T>(d.ToImmutable(), containsNull);
    }

    public static ISet<T> FromCollectionPlusOne(IEnumerable<T> values, T oneMoreValue) {
      var d = ImmutableHashSet<T>.Empty.ToBuilder();
      var containsNull = false;
      if (oneMoreValue == null) {
        containsNull = true;
      } else {
        d.Add(oneMoreValue);
      }

      foreach (T t in values) {
        if (t == null) {
          containsNull = true;
        } else {
          d.Add(t);
        }
      }

      return new Set<T>(d.ToImmutable(), containsNull);
    }

    public ISet<U> DowncastClone<U>(Func<T, U> converter) {
      if (this is ISet<U> th) {
        return th;
      } else {
        var d = ImmutableHashSet<U>.Empty.ToBuilder();
        foreach (var t in this.setImpl) {
          var u = converter(t);
          d.Add(u);
        }

        return new Set<U>(d.ToImmutable(), this.containsNull);
      }
    }

    public int Count {
      get { return this.setImpl.Count + (containsNull ? 1 : 0); }
    }

    public long LongCount {
      get { return this.setImpl.Count + (containsNull ? 1 : 0); }
    }

    public IEnumerable<T> Elements {
      get {
        if (containsNull) {
          yield return default(T);
        }

        foreach (var t in this.setImpl) {
          yield return t;
        }
      }
    }

    /// <summary>
    /// This is an inefficient iterator for producing all subsets of "this".
    /// </summary>
    public IEnumerable<ISet<T>> AllSubsets {
      get {
        // Start by putting all set elements into a list, but don't include null
        var elmts = new List<T>();
        elmts.AddRange(this.setImpl);
        var n = elmts.Count;
        var which = new bool[n];
        var s = ImmutableHashSet<T>.Empty.ToBuilder();
        while (true) {
          // yield both the subset without null and, if null is in the original set, the subset with null included
          var ihs = s.ToImmutable();
          yield return new Set<T>(ihs, false);
          if (containsNull) {
            yield return new Set<T>(ihs, true);
          }

          // "add 1" to "which", as if doing a carry chain.  For every digit changed, change the membership of the corresponding element in "s".
          int i = 0;
          for (; i < n && which[i]; i++) {
            which[i] = false;
            s.Remove(elmts[i]);
          }

          if (i == n) {
            // we have cycled through all the subsets
            break;
          }

          which[i] = true;
          s.Add(elmts[i]);
        }
      }
    }

    public bool Equals(ISet<T> other) {
      if (other == null || Count != other.Count) {
        return false;
      } else if (this == other) {
        return true;
      }

      foreach (var elmt in Elements) {
        if (!other.Contains(elmt)) {
          return false;
        }
      }

      return true;
    }

    public override bool Equals(object other) {
      if (other is ISet<T>) {
        return Equals((ISet<T>)other);
      }

      var th = this as ISet<object>;
      var oth = other as ISet<object>;
      if (th != null && oth != null) {
        // We'd like to obtain the more specific type parameter U for oth's type ISet<U>.
        // We do that by making a dynamically dispatched call, like:
        //     oth.Equals(this)
        // The hope is then that its comparison "this is ISet<U>" (that is, the first "if" test
        // above, but in the call "oth.Equals(this)") will be true and the non-virtual Equals
        // can be called. However, such a recursive call to "oth.Equals(this)" could turn
        // into infinite recursion. Therefore, we instead call "oth.EqualsAux(this)", which
        // performs the desired type test, but doesn't recurse any further.
        return oth.EqualsAux(th);
      } else {
        return false;
      }
    }

    public bool EqualsAux(ISet<object> other) {
      var s = other as ISet<T>;
      if (s != null) {
        return Equals(s);
      } else {
        return false;
      }
    }

    public override int GetHashCode() {
      var hashCode = 1;
      if (containsNull) {
        hashCode = hashCode * (Dafny.Helpers.GetHashCode(default(T)) + 3);
      }

      foreach (var t in this.setImpl) {
        hashCode = hashCode * (Dafny.Helpers.GetHashCode(t) + 3);
      }

      return hashCode;
    }

    public override string ToString() {
      var s = "{";
      var sep = "";
      if (containsNull) {
        s += sep + Dafny.Helpers.ToString(default(T));
        sep = ", ";
      }

      foreach (var t in this.setImpl) {
        s += sep + Dafny.Helpers.ToString(t);
        sep = ", ";
      }

      return s + "}";
    }
    public static bool IsProperSubsetOf(ISet<T> th, ISet<T> other) {
      return th.Count < other.Count && IsSubsetOf(th, other);
    }
    public static bool IsSubsetOf(ISet<T> th, ISet<T> other) {
      if (other.Count < th.Count) {
        return false;
      }
      foreach (T t in th.Elements) {
        if (!other.Contains(t)) {
          return false;
        }
      }
      return true;
    }
    public static bool IsDisjointFrom(ISet<T> th, ISet<T> other) {
      ISet<T> a, b;
      if (th.Count < other.Count) {
        a = th; b = other;
      } else {
        a = other; b = th;
      }
      foreach (T t in a.Elements) {
        if (b.Contains(t)) {
          return false;
        }
      }
      return true;
    }
    public bool Contains<G>(G t) {
      return t == null ? containsNull : t is T && this.setImpl.Contains((T)(object)t);
    }
    public static ISet<T> Union(ISet<T> th, ISet<T> other) {
      var a = FromISet(th);
      var b = FromISet(other);
      return new Set<T>(a.setImpl.Union(b.setImpl), a.containsNull || b.containsNull);
    }
    public static ISet<T> Intersect(ISet<T> th, ISet<T> other) {
      var a = FromISet(th);
      var b = FromISet(other);
      return new Set<T>(a.setImpl.Intersect(b.setImpl), a.containsNull && b.containsNull);
    }
    public static ISet<T> Difference(ISet<T> th, ISet<T> other) {
      var a = FromISet(th);
      var b = FromISet(other);
      return new Set<T>(a.setImpl.Except(b.setImpl), a.containsNull && !b.containsNull);
    }
  }

  public interface IMultiSet<out T> {
    bool IsEmpty { get; }
    int Count { get; }
    long LongCount { get; }
    IEnumerable<T> Elements { get; }
    IEnumerable<T> UniqueElements { get; }
    bool Contains<G>(G t);
    BigInteger Select<G>(G t);
    IMultiSet<T> Update<G>(G t, BigInteger i);
    bool EqualsAux(IMultiSet<object> other);
    IMultiSet<U> DowncastClone<U>(Func<T, U> converter);
  }

  public class MultiSet<T> : IMultiSet<T> {
    readonly ImmutableDictionary<T, BigInteger> dict;
    readonly BigInteger occurrencesOfNull;  // stupidly, a Dictionary in .NET cannot use "null" as a key
    MultiSet(ImmutableDictionary<T, BigInteger>.Builder d, BigInteger occurrencesOfNull) {
      dict = d.ToImmutable();
      this.occurrencesOfNull = occurrencesOfNull;
    }
    public static readonly MultiSet<T> Empty = new MultiSet<T>(ImmutableDictionary<T, BigInteger>.Empty.ToBuilder(), BigInteger.Zero);

    private static readonly TypeDescriptor<IMultiSet<T>> _TYPE = new Dafny.TypeDescriptor<IMultiSet<T>>(Empty);
    public static TypeDescriptor<IMultiSet<T>> _TypeDescriptor() {
      return _TYPE;
    }

    public static MultiSet<T> FromIMultiSet(IMultiSet<T> s) {
      return s as MultiSet<T> ?? FromCollection(s.Elements);
    }
    public static MultiSet<T> FromElements(params T[] values) {
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      var occurrencesOfNull = BigInteger.Zero;
      foreach (T t in values) {
        if (t == null) {
          occurrencesOfNull++;
        } else {
          BigInteger i;
          if (!d.TryGetValue(t, out i)) {
            i = BigInteger.Zero;
          }
          d[t] = i + 1;
        }
      }
      return new MultiSet<T>(d, occurrencesOfNull);
    }

    public static MultiSet<T> FromCollection(IEnumerable<T> values) {
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      var occurrencesOfNull = BigInteger.Zero;
      foreach (T t in values) {
        if (t == null) {
          occurrencesOfNull++;
        } else {
          BigInteger i;
          if (!d.TryGetValue(t,
            out i)) {
            i = BigInteger.Zero;
          }

          d[t] = i + 1;
        }
      }

      return new MultiSet<T>(d,
        occurrencesOfNull);
    }

    public static MultiSet<T> FromSeq(ISequence<T> values) {
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      var occurrencesOfNull = BigInteger.Zero;
      foreach (T t in values.Elements) {
        if (t == null) {
          occurrencesOfNull++;
        } else {
          BigInteger i;
          if (!d.TryGetValue(t,
            out i)) {
            i = BigInteger.Zero;
          }

          d[t] = i + 1;
        }
      }

      return new MultiSet<T>(d,
        occurrencesOfNull);
    }
    public static MultiSet<T> FromSet(ISet<T> values) {
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      var containsNull = false;
      foreach (T t in values.Elements) {
        if (t == null) {
          containsNull = true;
        } else {
          d[t] = BigInteger.One;
        }
      }
      return new MultiSet<T>(d, containsNull ? BigInteger.One : BigInteger.Zero);
    }
    public IMultiSet<U> DowncastClone<U>(Func<T, U> converter) {
      if (this is IMultiSet<U> th) {
        return th;
      } else {
        var d = ImmutableDictionary<U, BigInteger>.Empty.ToBuilder();
        foreach (var item in this.dict) {
          var k = converter(item.Key);
          d.Add(k, item.Value);
        }
        return new MultiSet<U>(d, this.occurrencesOfNull);
      }
    }

    public bool Equals(IMultiSet<T> other) {
      return IsSubsetOf(this, other) && IsSubsetOf(other, this);
    }
    public override bool Equals(object other) {
      if (other is IMultiSet<T>) {
        return Equals((IMultiSet<T>)other);
      }
      var th = this as IMultiSet<object>;
      var oth = other as IMultiSet<object>;
      if (th != null && oth != null) {
        // See comment in Set.Equals
        return oth.EqualsAux(th);
      } else {
        return false;
      }
    }

    public bool EqualsAux(IMultiSet<object> other) {
      var s = other as IMultiSet<T>;
      if (s != null) {
        return Equals(s);
      } else {
        return false;
      }
    }

    public override int GetHashCode() {
      var hashCode = 1;
      if (occurrencesOfNull > 0) {
        var key = Dafny.Helpers.GetHashCode(default(T));
        key = (key << 3) | (key >> 29) ^ occurrencesOfNull.GetHashCode();
        hashCode = hashCode * (key + 3);
      }
      foreach (var kv in dict) {
        var key = Dafny.Helpers.GetHashCode(kv.Key);
        key = (key << 3) | (key >> 29) ^ kv.Value.GetHashCode();
        hashCode = hashCode * (key + 3);
      }
      return hashCode;
    }
    public override string ToString() {
      var s = "multiset{";
      var sep = "";
      for (var i = BigInteger.Zero; i < occurrencesOfNull; i++) {
        s += sep + Dafny.Helpers.ToString(default(T));
        sep = ", ";
      }
      foreach (var kv in dict) {
        var t = Dafny.Helpers.ToString(kv.Key);
        for (var i = BigInteger.Zero; i < kv.Value; i++) {
          s += sep + t;
          sep = ", ";
        }
      }
      return s + "}";
    }
    public static bool IsProperSubsetOf(IMultiSet<T> th, IMultiSet<T> other) {
      return th.Count < other.Count && IsSubsetOf(th, other);
    }
    public static bool IsSubsetOf(IMultiSet<T> th, IMultiSet<T> other) {
      var a = FromIMultiSet(th);
      var b = FromIMultiSet(other);
      if (b.occurrencesOfNull < a.occurrencesOfNull) {
        return false;
      }
      foreach (T t in a.dict.Keys) {
        if (b.dict.ContainsKey(t)) {
          if (b.dict[t] < a.dict[t]) {
            return false;
          }
        } else {
          if (a.dict[t] != BigInteger.Zero) {
            return false;
          }
        }
      }
      return true;
    }
    public static bool IsDisjointFrom(IMultiSet<T> th, IMultiSet<T> other) {
      foreach (T t in th.UniqueElements) {
        if (other.Contains(t)) {
          return false;
        }
      }
      return true;
    }

    public bool Contains<G>(G t) {
      return Select(t) != 0;
    }
    public BigInteger Select<G>(G t) {
      if (t == null) {
        return occurrencesOfNull;
      }
      BigInteger m;
      if (t is T && dict.TryGetValue((T)(object)t, out m)) {
        return m;
      } else {
        return BigInteger.Zero;
      }
    }
    public IMultiSet<T> Update<G>(G t, BigInteger i) {
      if (Select(t) == i) {
        return this;
      } else if (t == null) {
        var r = dict.ToBuilder();
        return new MultiSet<T>(r, i);
      } else {
        var r = dict.ToBuilder();
        r[(T)(object)t] = i;
        return new MultiSet<T>(r, occurrencesOfNull);
      }
    }
    public static IMultiSet<T> Union(IMultiSet<T> th, IMultiSet<T> other) {
      if (th.IsEmpty) {
        return other;
      } else if (other.IsEmpty) {
        return th;
      }
      var a = FromIMultiSet(th);
      var b = FromIMultiSet(other);
      var r = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      foreach (T t in a.dict.Keys) {
        BigInteger i;
        if (!r.TryGetValue(t, out i)) {
          i = BigInteger.Zero;
        }
        r[t] = i + a.dict[t];
      }
      foreach (T t in b.dict.Keys) {
        BigInteger i;
        if (!r.TryGetValue(t, out i)) {
          i = BigInteger.Zero;
        }
        r[t] = i + b.dict[t];
      }
      return new MultiSet<T>(r, a.occurrencesOfNull + b.occurrencesOfNull);
    }
    public static IMultiSet<T> Intersect(IMultiSet<T> th, IMultiSet<T> other) {
      if (th.IsEmpty) {
        return th;
      } else if (other.IsEmpty) {
        return other;
      }
      var a = FromIMultiSet(th);
      var b = FromIMultiSet(other);
      var r = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      foreach (T t in a.dict.Keys) {
        if (b.dict.ContainsKey(t)) {
          r.Add(t, a.dict[t] < b.dict[t] ? a.dict[t] : b.dict[t]);
        }
      }
      return new MultiSet<T>(r, a.occurrencesOfNull < b.occurrencesOfNull ? a.occurrencesOfNull : b.occurrencesOfNull);
    }
    public static IMultiSet<T> Difference(IMultiSet<T> th, IMultiSet<T> other) { // \result == this - other
      if (other.IsEmpty) {
        return th;
      }
      var a = FromIMultiSet(th);
      var b = FromIMultiSet(other);
      var r = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      foreach (T t in a.dict.Keys) {
        if (!b.dict.ContainsKey(t)) {
          r.Add(t, a.dict[t]);
        } else if (b.dict[t] < a.dict[t]) {
          r.Add(t, a.dict[t] - b.dict[t]);
        }
      }
      return new MultiSet<T>(r, b.occurrencesOfNull < a.occurrencesOfNull ? a.occurrencesOfNull - b.occurrencesOfNull : BigInteger.Zero);
    }

    public bool IsEmpty { get { return occurrencesOfNull == 0 && dict.IsEmpty; } }

    public int Count {
      get { return (int)ElementCount(); }
    }
    public long LongCount {
      get { return (long)ElementCount(); }
    }
    private BigInteger ElementCount() {
      // This is inefficient
      var c = occurrencesOfNull;
      foreach (var item in dict) {
        c += item.Value;
      }
      return c;
    }

    public IEnumerable<T> Elements {
      get {
        for (var i = BigInteger.Zero; i < occurrencesOfNull; i++) {
          yield return default(T);
        }
        foreach (var item in dict) {
          for (var i = BigInteger.Zero; i < item.Value; i++) {
            yield return item.Key;
          }
        }
      }
    }

    public IEnumerable<T> UniqueElements {
      get {
        if (!occurrencesOfNull.IsZero) {
          yield return default(T);
        }
        foreach (var key in dict.Keys) {
          if (dict[key] != 0) {
            yield return key;
          }
        }
      }
    }
  }

  public interface IMap<out U, out V> {
    int Count { get; }
    long LongCount { get; }
    ISet<U> Keys { get; }
    ISet<V> Values { get; }
    IEnumerable<IPair<U, V>> ItemEnumerable { get; }
    bool Contains<G>(G t);
    /// <summary>
    /// Returns "true" iff "this is IMap<object, object>" and "this" equals "other".
    /// </summary>
    bool EqualsObjObj(IMap<object, object> other);
    IMap<UU, VV> DowncastClone<UU, VV>(Func<U, UU> keyConverter, Func<V, VV> valueConverter);
  }

  public class Map<U, V> : IMap<U, V> {
    readonly ImmutableDictionary<U, V> dict;
    readonly bool hasNullKey;  // true when "null" is a key of the Map
    readonly V nullValue;  // if "hasNullKey", the value that "null" maps to

    private Map(ImmutableDictionary<U, V>.Builder d, bool hasNullKey, V nullValue) {
      dict = d.ToImmutable();
      this.hasNullKey = hasNullKey;
      this.nullValue = nullValue;
    }
    public static readonly Map<U, V> Empty = new Map<U, V>(ImmutableDictionary<U, V>.Empty.ToBuilder(), false, default(V));

    private Map(ImmutableDictionary<U, V> d, bool hasNullKey, V nullValue) {
      dict = d;
      this.hasNullKey = hasNullKey;
      this.nullValue = nullValue;
    }

    private static readonly TypeDescriptor<IMap<U, V>> _TYPE = new Dafny.TypeDescriptor<IMap<U, V>>(Empty);
    public static TypeDescriptor<IMap<U, V>> _TypeDescriptor() {
      return _TYPE;
    }

    public static Map<U, V> FromElements(params IPair<U, V>[] values) {
      var d = ImmutableDictionary<U, V>.Empty.ToBuilder();
      var hasNullKey = false;
      var nullValue = default(V);
      foreach (var p in values) {
        if (p.Car == null) {
          hasNullKey = true;
          nullValue = p.Cdr;
        } else {
          d[p.Car] = p.Cdr;
        }
      }
      return new Map<U, V>(d, hasNullKey, nullValue);
    }
    public static Map<U, V> FromCollection(IEnumerable<IPair<U, V>> values) {
      var d = ImmutableDictionary<U, V>.Empty.ToBuilder();
      var hasNullKey = false;
      var nullValue = default(V);
      foreach (var p in values) {
        if (p.Car == null) {
          hasNullKey = true;
          nullValue = p.Cdr;
        } else {
          d[p.Car] = p.Cdr;
        }
      }
      return new Map<U, V>(d, hasNullKey, nullValue);
    }
    public static Map<U, V> FromIMap(IMap<U, V> m) {
      return m as Map<U, V> ?? FromCollection(m.ItemEnumerable);
    }
    public IMap<UU, VV> DowncastClone<UU, VV>(Func<U, UU> keyConverter, Func<V, VV> valueConverter) {
      if (this is IMap<UU, VV> th) {
        return th;
      } else {
        var d = ImmutableDictionary<UU, VV>.Empty.ToBuilder();
        foreach (var item in this.dict) {
          var k = keyConverter(item.Key);
          var v = valueConverter(item.Value);
          d.Add(k, v);
        }
        return new Map<UU, VV>(d, this.hasNullKey, (VV)(object)this.nullValue);
      }
    }
    public int Count {
      get { return dict.Count + (hasNullKey ? 1 : 0); }
    }
    public long LongCount {
      get { return dict.Count + (hasNullKey ? 1 : 0); }
    }

    public bool Equals(IMap<U, V> other) {
      if (other == null || LongCount != other.LongCount) {
        return false;
      } else if (this == other) {
        return true;
      }
      if (hasNullKey) {
        if (!other.Contains(default(U)) || !object.Equals(nullValue, Select(other, default(U)))) {
          return false;
        }
      }
      foreach (var item in dict) {
        if (!other.Contains(item.Key) || !object.Equals(item.Value, Select(other, item.Key))) {
          return false;
        }
      }
      return true;
    }
    public bool EqualsObjObj(IMap<object, object> other) {
      if (!(this is IMap<object, object>) || other == null || LongCount != other.LongCount) {
        return false;
      } else if (this == other) {
        return true;
      }
      var oth = Map<object, object>.FromIMap(other);
      if (hasNullKey) {
        if (!oth.Contains(default(U)) || !object.Equals(nullValue, Map<object, object>.Select(oth, default(U)))) {
          return false;
        }
      }
      foreach (var item in dict) {
        if (!other.Contains(item.Key) || !object.Equals(item.Value, Map<object, object>.Select(oth, item.Key))) {
          return false;
        }
      }
      return true;
    }
    public override bool Equals(object other) {
      // See comment in Set.Equals
      var m = other as IMap<U, V>;
      if (m != null) {
        return Equals(m);
      }
      var imapoo = other as IMap<object, object>;
      if (imapoo != null) {
        return EqualsObjObj(imapoo);
      } else {
        return false;
      }
    }

    public override int GetHashCode() {
      var hashCode = 1;
      if (hasNullKey) {
        var key = Dafny.Helpers.GetHashCode(default(U));
        key = (key << 3) | (key >> 29) ^ Dafny.Helpers.GetHashCode(nullValue);
        hashCode = hashCode * (key + 3);
      }
      foreach (var kv in dict) {
        var key = Dafny.Helpers.GetHashCode(kv.Key);
        key = (key << 3) | (key >> 29) ^ Dafny.Helpers.GetHashCode(kv.Value);
        hashCode = hashCode * (key + 3);
      }
      return hashCode;
    }
    public override string ToString() {
      var s = "map[";
      var sep = "";
      if (hasNullKey) {
        s += sep + Dafny.Helpers.ToString(default(U)) + " := " + Dafny.Helpers.ToString(nullValue);
        sep = ", ";
      }
      foreach (var kv in dict) {
        s += sep + Dafny.Helpers.ToString(kv.Key) + " := " + Dafny.Helpers.ToString(kv.Value);
        sep = ", ";
      }
      return s + "]";
    }
    public bool Contains<G>(G u) {
      return u == null ? hasNullKey : u is U && dict.ContainsKey((U)(object)u);
    }
    public static V Select(IMap<U, V> th, U index) {
      // the following will throw an exception if "index" in not a key of the map
      var m = FromIMap(th);
      return index == null && m.hasNullKey ? m.nullValue : m.dict[index];
    }
    public static IMap<U, V> Update(IMap<U, V> th, U index, V val) {
      var m = FromIMap(th);
      var d = m.dict.ToBuilder();
      if (index == null) {
        return new Map<U, V>(d, true, val);
      } else {
        d[index] = val;
        return new Map<U, V>(d, m.hasNullKey, m.nullValue);
      }
    }

    public static IMap<U, V> Merge(IMap<U, V> th, IMap<U, V> other) {
      var a = FromIMap(th);
      var b = FromIMap(other);
      ImmutableDictionary<U, V> d = a.dict.SetItems(b.dict);
      return new Map<U, V>(d, a.hasNullKey || b.hasNullKey, b.hasNullKey ? b.nullValue : a.nullValue);
    }

    public static IMap<U, V> Subtract(IMap<U, V> th, ISet<U> keys) {
      var a = FromIMap(th);
      ImmutableDictionary<U, V> d = a.dict.RemoveRange(keys.Elements);
      return new Map<U, V>(d, a.hasNullKey && !keys.Contains<object>(null), a.nullValue);
    }

    public ISet<U> Keys {
      get {
        if (hasNullKey) {
          return Dafny.Set<U>.FromCollectionPlusOne(dict.Keys, default(U));
        } else {
          return Dafny.Set<U>.FromCollection(dict.Keys);
        }
      }
    }
    public ISet<V> Values {
      get {
        if (hasNullKey) {
          return Dafny.Set<V>.FromCollectionPlusOne(dict.Values, nullValue);
        } else {
          return Dafny.Set<V>.FromCollection(dict.Values);
        }
      }
    }

    public IEnumerable<IPair<U, V>> ItemEnumerable {
      get {
        if (hasNullKey) {
          yield return new Pair<U, V>(default(U), nullValue);
        }
        foreach (KeyValuePair<U, V> kvp in dict) {
          yield return new Pair<U, V>(kvp.Key, kvp.Value);
        }
      }
    }

    public static ISet<_System._ITuple2<U, V>> Items(IMap<U, V> m) {
      var result = new HashSet<_System._ITuple2<U, V>>();
      foreach (var item in m.ItemEnumerable) {
        result.Add(_System.Tuple2<U, V>.create(item.Car, item.Cdr));
      }
      return Dafny.Set<_System._ITuple2<U, V>>.FromCollection(result);
    }
  }

  public interface ISequence<out T> {
    long LongCount { get; }
    int Count { get; }
    T[] Elements { get; }
    IEnumerable<T> UniqueElements { get; }
    T Select(ulong index);
    T Select(long index);
    T Select(uint index);
    T Select(int index);
    T Select(BigInteger index);
    bool Contains<G>(G g);
    ISequence<T> Take(long m);
    ISequence<T> Take(ulong n);
    ISequence<T> Take(BigInteger n);
    ISequence<T> Drop(long m);
    ISequence<T> Drop(ulong n);
    ISequence<T> Drop(BigInteger n);
    ISequence<T> Subsequence(long lo, long hi);
    ISequence<T> Subsequence(long lo, ulong hi);
    ISequence<T> Subsequence(long lo, BigInteger hi);
    ISequence<T> Subsequence(ulong lo, long hi);
    ISequence<T> Subsequence(ulong lo, ulong hi);
    ISequence<T> Subsequence(ulong lo, BigInteger hi);
    ISequence<T> Subsequence(BigInteger lo, long hi);
    ISequence<T> Subsequence(BigInteger lo, ulong hi);
    ISequence<T> Subsequence(BigInteger lo, BigInteger hi);
    bool EqualsAux(ISequence<object> other);
    ISequence<U> DowncastClone<U>(Func<T, U> converter);
  }

  public abstract class Sequence<T> : ISequence<T> {
    public static readonly ISequence<T> Empty = new ArraySequence<T>(new T[0]);

    private static readonly TypeDescriptor<ISequence<T>> _TYPE = new Dafny.TypeDescriptor<ISequence<T>>(Empty);
    public static TypeDescriptor<ISequence<T>> _TypeDescriptor() {
      return _TYPE;
    }

    public static ISequence<T> Create(BigInteger length, System.Func<BigInteger, T> init) {
      var len = (int)length;
      var values = new T[len];
      for (int i = 0; i < len; i++) {
        values[i] = init(new BigInteger(i));
      }
      return new ArraySequence<T>(values);
    }
    public static ISequence<T> FromArray(T[] values) {
      return new ArraySequence<T>(values);
    }
    public static ISequence<T> FromElements(params T[] values) {
      return new ArraySequence<T>(values);
    }
    public static ISequence<char> FromString(string s) {
      return new ArraySequence<char>(s.ToCharArray());
    }
    public ISequence<U> DowncastClone<U>(Func<T, U> converter) {
      if (this is ISequence<U> th) {
        return th;
      } else {
        var values = new U[this.LongCount];
        for (long i = 0; i < this.LongCount; i++) {
          var val = converter(this.Select(i));
          values[i] = val;
        }
        return new ArraySequence<U>(values);
      }
    }
    public static ISequence<T> Update(ISequence<T> sequence, long index, T t) {
      T[] tmp = (T[])sequence.Elements.Clone();
      tmp[index] = t;
      return new ArraySequence<T>(tmp);
    }
    public static ISequence<T> Update(ISequence<T> sequence, ulong index, T t) {
      return Update(sequence, (long)index, t);
    }
    public static ISequence<T> Update(ISequence<T> sequence, BigInteger index, T t) {
      return Update(sequence, (long)index, t);
    }
    public static bool EqualUntil(ISequence<T> left, ISequence<T> right, int n) {
      T[] leftElmts = left.Elements, rightElmts = right.Elements;
      for (int i = 0; i < n; i++) {
        if (!object.Equals(leftElmts[i], rightElmts[i])) {
          return false;
        }
      }
      return true;
    }
    public static bool IsPrefixOf(ISequence<T> left, ISequence<T> right) {
      int n = left.Elements.Length;
      return n <= right.Elements.Length && EqualUntil(left, right, n);
    }
    public static bool IsProperPrefixOf(ISequence<T> left, ISequence<T> right) {
      int n = left.Elements.Length;
      return n < right.Elements.Length && EqualUntil(left, right, n);
    }
    public static ISequence<T> Concat(ISequence<T> left, ISequence<T> right) {
      if (left.Count == 0) {
        return right;
      }
      if (right.Count == 0) {
        return left;
      }
      return new ConcatSequence<T>(left, right);
    }
    // Make Count a public abstract instead of LongCount, since the "array size is limited to a total of 4 billion
    // elements, and to a maximum index of 0X7FEFFFFF". Therefore, as a protection, limit this to int32.
    // https://docs.microsoft.com/en-us/dotnet/api/system.array
    public abstract int Count { get; }
    public long LongCount {
      get { return Count; }
    }
    // ImmutableElements cannot be public in the interface since ImmutableArray<T> leads to a
    // "covariant type T occurs in invariant position" error. There do not appear to be interfaces for ImmutableArray<T>
    // that resolve this.
    protected abstract ImmutableArray<T> ImmutableElements { get; }

    public T[] Elements {
      get { return ImmutableElements.ToArray(); }
    }
    public IEnumerable<T> UniqueElements {
      get {
        var st = Set<T>.FromCollection(ImmutableElements);
        return st.Elements;
      }
    }

    public T Select(ulong index) {
      return ImmutableElements[checked((int)index)];
    }
    public T Select(long index) {
      return ImmutableElements[checked((int)index)];
    }
    public T Select(uint index) {
      return ImmutableElements[checked((int)index)];
    }
    public T Select(int index) {
      return ImmutableElements[index];
    }
    public T Select(BigInteger index) {
      return ImmutableElements[(int)index];
    }
    public bool Equals(ISequence<T> other) {
      int n = ImmutableElements.Length;
      return n == other.Elements.Length && EqualUntil(this, other, n);
    }
    public override bool Equals(object other) {
      if (other is ISequence<T>) {
        return Equals((ISequence<T>)other);
      }
      var th = this as ISequence<object>;
      var oth = other as ISequence<object>;
      if (th != null && oth != null) {
        // see explanation in Set.Equals
        return oth.EqualsAux(th);
      } else {
        return false;
      }
    }
    public bool EqualsAux(ISequence<object> other) {
      var s = other as ISequence<T>;
      if (s != null) {
        return Equals(s);
      } else {
        return false;
      }
    }
    public override int GetHashCode() {
      ImmutableArray<T> elmts = ImmutableElements;
      // https://devblogs.microsoft.com/dotnet/please-welcome-immutablearrayt/
      if (elmts.IsDefaultOrEmpty) {
        return 0;
      }

      var hashCode = 0;
      for (var i = 0; i < elmts.Length; i++) {
        hashCode = (hashCode << 3) | (hashCode >> 29) ^ Dafny.Helpers.GetHashCode(elmts[i]);
      }
      return hashCode;
    }
    public override string ToString() {
      // This is required because (ImmutableElements is ImmutableArray<char>) is not a valid type check
      var typeCheckTmp = new T[0];
      ImmutableArray<T> elmts = ImmutableElements;
      if (typeCheckTmp is char[]) {
        var s = "";
        foreach (var t in elmts) {
          s += t.ToString();
        }
        return s;
      } else {
        var s = "[";
        var sep = "";
        foreach (var t in elmts) {
          s += sep + Dafny.Helpers.ToString(t);
          sep = ", ";
        }
        return s + "]";
      }
    }
    public bool Contains<G>(G g) {
      if (g == null || g is T) {
        var t = (T)(object)g;
        return ImmutableElements.Contains(t);
      }
      return false;
    }
    public ISequence<T> Take(long m) {
      if (ImmutableElements.Length == m) {
        return this;
      }

      int length = checked((int)m);
      T[] tmp = new T[length];
      ImmutableElements.CopyTo(0, tmp, 0, length);
      return new ArraySequence<T>(tmp);
    }
    public ISequence<T> Take(ulong n) {
      return Take((long)n);
    }
    public ISequence<T> Take(BigInteger n) {
      return Take((long)n);
    }
    public ISequence<T> Drop(long m) {
      int startingElement = checked((int)m);
      if (startingElement == 0) {
        return this;
      }

      int length = ImmutableElements.Length - startingElement;
      T[] tmp = new T[length];
      ImmutableElements.CopyTo(startingElement, tmp, 0, length);
      return new ArraySequence<T>(tmp);
    }
    public ISequence<T> Drop(ulong n) {
      return Drop((long)n);
    }
    public ISequence<T> Drop(BigInteger n) {
      if (n.IsZero) {
        return this;
      }

      return Drop((long)n);
    }
    public ISequence<T> Subsequence(long lo, long hi) {
      if (lo == 0 && hi == ImmutableElements.Length) {
        return this;
      }
      int startingIndex = checked((int)lo);
      int endingIndex = checked((int)hi);
      var length = endingIndex - startingIndex;
      T[] tmp = new T[length];
      ImmutableElements.CopyTo(startingIndex, tmp, 0, length);
      return new ArraySequence<T>(tmp);
    }
    public ISequence<T> Subsequence(long lo, ulong hi) {
      return Subsequence(lo, (long)hi);
    }
    public ISequence<T> Subsequence(long lo, BigInteger hi) {
      return Subsequence(lo, (long)hi);
    }
    public ISequence<T> Subsequence(ulong lo, long hi) {
      return Subsequence((long)lo, hi);
    }
    public ISequence<T> Subsequence(ulong lo, ulong hi) {
      return Subsequence((long)lo, (long)hi);
    }
    public ISequence<T> Subsequence(ulong lo, BigInteger hi) {
      return Subsequence((long)lo, (long)hi);
    }
    public ISequence<T> Subsequence(BigInteger lo, long hi) {
      return Subsequence((long)lo, hi);
    }
    public ISequence<T> Subsequence(BigInteger lo, ulong hi) {
      return Subsequence((long)lo, (long)hi);
    }
    public ISequence<T> Subsequence(BigInteger lo, BigInteger hi) {
      return Subsequence((long)lo, (long)hi);
    }
  }

  internal class ArraySequence<T> : Sequence<T> {
    private readonly ImmutableArray<T> elmts;

    internal ArraySequence(ImmutableArray<T> ee) {
      elmts = ee;
    }
    internal ArraySequence(T[] ee) {
      elmts = ImmutableArray.Create<T>(ee);
    }

    protected override ImmutableArray<T> ImmutableElements {
      get {
        return elmts;
      }
    }
    public override int Count {
      get {
        return elmts.Length;
      }
    }
  }

  internal class ConcatSequence<T> : Sequence<T> {
    // INVARIANT: Either left != null, right != null, and elmts's underlying array == null or
    // left == null, right == null, and elmts's underlying array != null
    private volatile ISequence<T> left, right;
    private ImmutableArray<T> elmts;
    private readonly int count;

    internal ConcatSequence(ISequence<T> left, ISequence<T> right) {
      this.left = left;
      this.right = right;
      this.count = left.Count + right.Count;
    }

    protected override ImmutableArray<T> ImmutableElements {
      get {
        // IsDefault returns true if the underlying array is a null reference
        // https://devblogs.microsoft.com/dotnet/please-welcome-immutablearrayt/
        if (elmts.IsDefault) {
          elmts = ComputeElements();
          // We don't need the original sequences anymore; let them be
          // garbage-collected
          left = null;
          right = null;
        }
        return elmts;
      }
    }

    public override int Count {
      get {
        return count;
      }
    }

    private ImmutableArray<T> ComputeElements() {
      // Traverse the tree formed by all descendants which are ConcatSequences
      var ansBuilder = ImmutableArray.CreateBuilder<T>(count);
      var toVisit = new Stack<ISequence<T>>();
      var (leftBuffer, rightBuffer) = (left, right);
      if (left == null || right == null) {
        // elmts can't be .IsDefault while either left, or right are null
        return elmts;
      }
      toVisit.Push(rightBuffer);
      toVisit.Push(leftBuffer);

      while (toVisit.Count != 0) {
        var seq = toVisit.Pop();
        if (seq is ConcatSequence<T> cs && cs.elmts.IsDefault) {
          (leftBuffer, rightBuffer) = (cs.left, cs.right);
          if (cs.left == null || cs.right == null) {
            // !cs.elmts.IsDefault, due to concurrent enumeration
            toVisit.Push(cs);
          } else {
            toVisit.Push(rightBuffer);
            toVisit.Push(leftBuffer);
          }
        } else {
          var array = seq.Elements;
          ansBuilder.AddRange(array);
        }
      }
      return ansBuilder.ToImmutable();
    }
  }

  public interface IPair<out A, out B> {
    A Car { get; }
    B Cdr { get; }
  }

  public class Pair<A, B> : IPair<A, B> {
    private A car;
    private B cdr;
    public A Car { get { return car; } }
    public B Cdr { get { return cdr; } }
    public Pair(A a, B b) {
      this.car = a;
      this.cdr = b;
    }
  }

  public class TypeDescriptor<T> {
    private readonly T initValue;
    public TypeDescriptor(T initValue) {
      this.initValue = initValue;
    }
    public T Default() {
      return initValue;
    }
  }

  public partial class Helpers {
    public static int GetHashCode<G>(G g) {
      return g == null ? 1001 : g.GetHashCode();
    }

    public static int ToIntChecked(BigInteger i, string msg) {
      if (i > Int32.MaxValue || i < Int32.MinValue) {
        if (msg == null) {
          msg = "value out of range for a 32-bit int";
        }

        throw new HaltException(msg + ": " + i);
      }
      return (int)i;
    }
    public static int ToIntChecked(long i, string msg) {
      if (i > Int32.MaxValue || i < Int32.MinValue) {
        if (msg == null) {
          msg = "value out of range for a 32-bit int";
        }

        throw new HaltException(msg + ": " + i);
      }
      return (int)i;
    }
    public static int ToIntChecked(int i, string msg) {
      return i;
    }

    public static string ToString<G>(G g) {
      if (g == null) {
        return "null";
      } else if (g is bool) {
        return (bool)(object)g ? "true" : "false";  // capitalize boolean literals like in Dafny
      } else {
        return g.ToString();
      }
    }
    public static void Print<G>(G g) {
      System.Console.Write(ToString(g));
    }

    public static readonly TypeDescriptor<bool> BOOL = new TypeDescriptor<bool>(false);
    public static readonly TypeDescriptor<char> CHAR = new TypeDescriptor<char>('D');  // See CharType.DefaultValue in Dafny source code
    public static readonly TypeDescriptor<BigInteger> INT = new TypeDescriptor<BigInteger>(BigInteger.Zero);
    public static readonly TypeDescriptor<BigRational> REAL = new TypeDescriptor<BigRational>(BigRational.ZERO);
    public static readonly TypeDescriptor<byte> UINT8 = new TypeDescriptor<byte>(0);
    public static readonly TypeDescriptor<ushort> UINT16 = new TypeDescriptor<ushort>(0);
    public static readonly TypeDescriptor<uint> UINT32 = new TypeDescriptor<uint>(0);
    public static readonly TypeDescriptor<ulong> UINT64 = new TypeDescriptor<ulong>(0);

    public static TypeDescriptor<T> NULL<T>() where T : class {
      return new TypeDescriptor<T>(null);
    }

    public static TypeDescriptor<A[]> ARRAY<A>() {
      return new TypeDescriptor<A[]>(new A[0]);
    }

    public static bool Quantifier<T>(IEnumerable<T> vals, bool frall, System.Predicate<T> pred) {
      foreach (var u in vals) {
        if (pred(u) != frall) { return !frall; }
      }
      return frall;
    }
    // Enumerating other collections
    public static IEnumerable<bool> AllBooleans() {
      yield return false;
      yield return true;
    }
    public static IEnumerable<char> AllChars() {
      for (int i = 0; i < 0x10000; i++) {
        yield return (char)i;
      }
    }
    public static IEnumerable<BigInteger> AllIntegers() {
      yield return new BigInteger(0);
      for (var j = new BigInteger(1); ; j++) {
        yield return j;
        yield return -j;
      }
    }
    public static IEnumerable<BigInteger> IntegerRange(Nullable<BigInteger> lo, Nullable<BigInteger> hi) {
      if (lo == null) {
        for (var j = (BigInteger)hi; true;) {
          j--;
          yield return j;
        }
      } else if (hi == null) {
        for (var j = (BigInteger)lo; true; j++) {
          yield return j;
        }
      } else {
        for (var j = (BigInteger)lo; j < hi; j++) {
          yield return j;
        }
      }
    }
    public static IEnumerable<T> SingleValue<T>(T e) {
      yield return e;
    }
    // pre: b != 0
    // post: result == a/b, as defined by Euclidean Division (http://en.wikipedia.org/wiki/Modulo_operation)
    public static sbyte EuclideanDivision_sbyte(sbyte a, sbyte b) {
      return (sbyte)EuclideanDivision_int(a, b);
    }
    public static short EuclideanDivision_short(short a, short b) {
      return (short)EuclideanDivision_int(a, b);
    }
    public static int EuclideanDivision_int(int a, int b) {
      if (0 <= a) {
        if (0 <= b) {
          // +a +b: a/b
          return (int)(((uint)(a)) / ((uint)(b)));
        } else {
          // +a -b: -(a/(-b))
          return -((int)(((uint)(a)) / ((uint)(unchecked(-b)))));
        }
      } else {
        if (0 <= b) {
          // -a +b: -((-a-1)/b) - 1
          return -((int)(((uint)(-(a + 1))) / ((uint)(b)))) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return ((int)(((uint)(-(a + 1))) / ((uint)(unchecked(-b))))) + 1;
        }
      }
    }
    public static long EuclideanDivision_long(long a, long b) {
      if (0 <= a) {
        if (0 <= b) {
          // +a +b: a/b
          return (long)(((ulong)(a)) / ((ulong)(b)));
        } else {
          // +a -b: -(a/(-b))
          return -((long)(((ulong)(a)) / ((ulong)(unchecked(-b)))));
        }
      } else {
        if (0 <= b) {
          // -a +b: -((-a-1)/b) - 1
          return -((long)(((ulong)(-(a + 1))) / ((ulong)(b)))) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return ((long)(((ulong)(-(a + 1))) / ((ulong)(unchecked(-b))))) + 1;
        }
      }
    }
    public static BigInteger EuclideanDivision(BigInteger a, BigInteger b) {
      if (0 <= a.Sign) {
        if (0 <= b.Sign) {
          // +a +b: a/b
          return BigInteger.Divide(a, b);
        } else {
          // +a -b: -(a/(-b))
          return BigInteger.Negate(BigInteger.Divide(a, BigInteger.Negate(b)));
        }
      } else {
        if (0 <= b.Sign) {
          // -a +b: -((-a-1)/b) - 1
          return BigInteger.Negate(BigInteger.Divide(BigInteger.Negate(a) - 1, b)) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return BigInteger.Divide(BigInteger.Negate(a) - 1, BigInteger.Negate(b)) + 1;
        }
      }
    }
    // pre: b != 0
    // post: result == a%b, as defined by Euclidean Division (http://en.wikipedia.org/wiki/Modulo_operation)
    public static sbyte EuclideanModulus_sbyte(sbyte a, sbyte b) {
      return (sbyte)EuclideanModulus_int(a, b);
    }
    public static short EuclideanModulus_short(short a, short b) {
      return (short)EuclideanModulus_int(a, b);
    }
    public static int EuclideanModulus_int(int a, int b) {
      uint bp = (0 <= b) ? (uint)b : (uint)(unchecked(-b));
      if (0 <= a) {
        // +a: a % b'
        return (int)(((uint)a) % bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        uint c = ((uint)(unchecked(-a))) % bp;
        return (int)(c == 0 ? c : bp - c);
      }
    }
    public static long EuclideanModulus_long(long a, long b) {
      ulong bp = (0 <= b) ? (ulong)b : (ulong)(unchecked(-b));
      if (0 <= a) {
        // +a: a % b'
        return (long)(((ulong)a) % bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        ulong c = ((ulong)(unchecked(-a))) % bp;
        return (long)(c == 0 ? c : bp - c);
      }
    }
    public static BigInteger EuclideanModulus(BigInteger a, BigInteger b) {
      var bp = BigInteger.Abs(b);
      if (0 <= a.Sign) {
        // +a: a % b'
        return BigInteger.Remainder(a, bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        var c = BigInteger.Remainder(BigInteger.Negate(a), bp);
        return c.IsZero ? c : BigInteger.Subtract(bp, c);
      }
    }

    public static U CastConverter<T, U>(T t) {
      return (U)(object)t;
    }

    public static Sequence<T> SeqFromArray<T>(T[] array) {
      return new ArraySequence<T>((T[])array.Clone());
    }
    // In .NET version 4.5, it is possible to mark a method with "AggressiveInlining", which says to inline the
    // method if possible.  Method "ExpressionSequence" would be a good candidate for it:
    // [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.AggressiveInlining)]
    public static U ExpressionSequence<T, U>(T t, U u) {
      return u;
    }

    public static U Let<T, U>(T t, Func<T, U> f) {
      return f(t);
    }

    public static A Id<A>(A a) {
      return a;
    }

    public static void WithHaltHandling(Action action) {
      try {
        action();
      } catch (HaltException e) {
        Console.WriteLine("[Program halted] " + e.Message);
      }
    }
  }

  public class BigOrdinal {
    public static bool IsLimit(BigInteger ord) {
      return ord == 0;
    }
    public static bool IsSucc(BigInteger ord) {
      return 0 < ord;
    }
    public static BigInteger Offset(BigInteger ord) {
      return ord;
    }
    public static bool IsNat(BigInteger ord) {
      return true;  // at run time, every ORDINAL is a natural number
    }
  }

  public struct BigRational {
    public static readonly BigRational ZERO = new BigRational(0);

    // We need to deal with the special case "num == 0 && den == 0", because
    // that's what C#'s default struct constructor will produce for BigRational. :(
    // To deal with it, we ignore "den" when "num" is 0.
    BigInteger num, den;  // invariant 1 <= den || (num == 0 && den == 0)
    public override string ToString() {
      int log10;
      if (num.IsZero || den.IsOne) {
        return string.Format("{0}.0", num);
      } else if (IsPowerOf10(den, out log10)) {
        string sign;
        string digits;
        if (num.Sign < 0) {
          sign = "-"; digits = (-num).ToString();
        } else {
          sign = ""; digits = num.ToString();
        }
        if (log10 < digits.Length) {
          var n = digits.Length - log10;
          return string.Format("{0}{1}.{2}", sign, digits.Substring(0, n), digits.Substring(n));
        } else {
          return string.Format("{0}0.{1}{2}", sign, new string('0', log10 - digits.Length), digits);
        }
      } else {
        return string.Format("({0}.0 / {1}.0)", num, den);
      }
    }
    public bool IsPowerOf10(BigInteger x, out int log10) {
      log10 = 0;
      if (x.IsZero) {
        return false;
      }
      while (true) {  // invariant: x != 0 && x * 10^log10 == old(x)
        if (x.IsOne) {
          return true;
        } else if (x % 10 == 0) {
          log10++;
          x /= 10;
        } else {
          return false;
        }
      }
    }
    public BigRational(int n) {
      num = new BigInteger(n);
      den = BigInteger.One;
    }
    public BigRational(BigInteger n, BigInteger d) {
      // requires 1 <= d
      num = n;
      den = d;
    }
    public BigInteger ToBigInteger() {
      if (num.IsZero || den.IsOne) {
        return num;
      } else if (0 < num.Sign) {
        return num / den;
      } else {
        return (num - den + 1) / den;
      }
    }
    /// <summary>
    /// Returns values such that aa/dd == a and bb/dd == b.
    /// </summary>
    private static void Normalize(BigRational a, BigRational b, out BigInteger aa, out BigInteger bb, out BigInteger dd) {
      if (a.num.IsZero) {
        aa = a.num;
        bb = b.num;
        dd = b.den;
      } else if (b.num.IsZero) {
        aa = a.num;
        dd = a.den;
        bb = b.num;
      } else {
        var gcd = BigInteger.GreatestCommonDivisor(a.den, b.den);
        var xx = a.den / gcd;
        var yy = b.den / gcd;
        // We now have a == a.num / (xx * gcd) and b == b.num / (yy * gcd).
        aa = a.num * yy;
        bb = b.num * xx;
        dd = a.den * yy;
      }
    }
    public int CompareTo(BigRational that) {
      // simple things first
      int asign = this.num.Sign;
      int bsign = that.num.Sign;
      if (asign < 0 && 0 <= bsign) {
        return -1;
      } else if (asign <= 0 && 0 < bsign) {
        return -1;
      } else if (bsign < 0 && 0 <= asign) {
        return 1;
      } else if (bsign <= 0 && 0 < asign) {
        return 1;
      }
      BigInteger aa, bb, dd;
      Normalize(this, that, out aa, out bb, out dd);
      return aa.CompareTo(bb);
    }
    public int Sign {
      get {
        return num.Sign;
      }
    }
    public override int GetHashCode() {
      return num.GetHashCode() + 29 * den.GetHashCode();
    }
    public override bool Equals(object obj) {
      if (obj is BigRational) {
        return this == (BigRational)obj;
      } else {
        return false;
      }
    }
    public static bool operator ==(BigRational a, BigRational b) {
      return a.CompareTo(b) == 0;
    }
    public static bool operator !=(BigRational a, BigRational b) {
      return a.CompareTo(b) != 0;
    }
    public static bool operator >(BigRational a, BigRational b) {
      return a.CompareTo(b) > 0;
    }
    public static bool operator >=(BigRational a, BigRational b) {
      return a.CompareTo(b) >= 0;
    }
    public static bool operator <(BigRational a, BigRational b) {
      return a.CompareTo(b) < 0;
    }
    public static bool operator <=(BigRational a, BigRational b) {
      return a.CompareTo(b) <= 0;
    }
    public static BigRational operator +(BigRational a, BigRational b) {
      BigInteger aa, bb, dd;
      Normalize(a, b, out aa, out bb, out dd);
      return new BigRational(aa + bb, dd);
    }
    public static BigRational operator -(BigRational a, BigRational b) {
      BigInteger aa, bb, dd;
      Normalize(a, b, out aa, out bb, out dd);
      return new BigRational(aa - bb, dd);
    }
    public static BigRational operator -(BigRational a) {
      return new BigRational(-a.num, a.den);
    }
    public static BigRational operator *(BigRational a, BigRational b) {
      return new BigRational(a.num * b.num, a.den * b.den);
    }
    public static BigRational operator /(BigRational a, BigRational b) {
      // Compute the reciprocal of b
      BigRational bReciprocal;
      if (0 < b.num.Sign) {
        bReciprocal = new BigRational(b.den, b.num);
      } else {
        // this is the case b.num < 0
        bReciprocal = new BigRational(-b.den, -b.num);
      }
      return a * bReciprocal;
    }
  }

  public class HaltException : Exception {
    public HaltException(object message) : base(message.ToString()) {
    }
  }
}

namespace @_System {
  public interface _ITuple2<out T0, out T1> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
  }

  public class Tuple2<T0, T1> : _ITuple2<T0, T1> {
    public readonly T0 _0;
    public readonly T1 _1;
    public Tuple2(T0 _0, T1 _1) {
      this._0 = _0;
      this._1 = _1;
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple2<T0, T1>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ")";
      return s;
    }
    public static _ITuple2<T0, T1> Default(T0 _default_T0, T1 _default_T1) {
      return create(_default_T0, _default_T1);
    }
    public static Dafny.TypeDescriptor<_System._ITuple2<T0, T1>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1) {
      return new Dafny.TypeDescriptor<_System._ITuple2<T0, T1>>(_System.Tuple2<T0, T1>.Default(_td_T0.Default(), _td_T1.Default()));
    }
    public static _ITuple2<T0, T1> create(T0 _0, T1 _1) {
      return new Tuple2<T0, T1>(_0, _1);
    }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
  }

} // end of namespace _System
namespace Dafny {
  internal class ArrayHelpers {
    public static T[] InitNewArray1<T>(T z, BigInteger size0) {
      int s0 = (int)size0;
      T[] a = new T[s0];
      for (int i0 = 0; i0 < s0; i0++) {
        a[i0] = z;
      }
      return a;
    }
  }
} // end of namespace Dafny
public static class FuncExtensions {
  public static Func<U, UResult> DowncastClone<T, TResult, U, UResult>(this Func<T, TResult> F, Func<U, T> ArgConv, Func<TResult, UResult> ResConv) {
    return arg => ResConv(F(ArgConv(arg)));
  }
  public static Func<UResult> DowncastClone<TResult, UResult>(this Func<TResult> F, Func<TResult, UResult> ResConv) {
    return () => ResConv(F());
  }
  public static Func<U1, U2, U3, U4, UResult> DowncastClone<T1, T2, T3, T4, TResult, U1, U2, U3, U4, UResult>(this Func<T1, T2, T3, T4, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4)));
  }
  public static Func<U1, U2, UResult> DowncastClone<T1, T2, TResult, U1, U2, UResult>(this Func<T1, T2, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<TResult, UResult> ResConv) {
    return (arg1, arg2) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2)));
  }
  public static Func<U1, U2, U3, UResult> DowncastClone<T1, T2, T3, TResult, U1, U2, U3, UResult>(this Func<T1, T2, T3, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3)));
  }
}
namespace _System {

  public partial class nat {
    private static readonly Dafny.TypeDescriptor<BigInteger> _TYPE = new Dafny.TypeDescriptor<BigInteger>(BigInteger.Zero);
    public static Dafny.TypeDescriptor<BigInteger> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public interface _ITuple0 {
    _ITuple0 DowncastClone();
  }
  public class Tuple0 : _ITuple0 {
    public Tuple0() {
    }
    public _ITuple0 DowncastClone() {
      if (this is _ITuple0 dt) { return dt; }
      return new Tuple0();
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple0;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      return "()";
    }
    private static readonly _ITuple0 theDefault = create();
    public static _ITuple0 Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<_System._ITuple0> _TYPE = new Dafny.TypeDescriptor<_System._ITuple0>(_System.Tuple0.Default());
    public static Dafny.TypeDescriptor<_System._ITuple0> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ITuple0 create() {
      return new Tuple0();
    }
    public static System.Collections.Generic.IEnumerable<_ITuple0> AllSingletonConstructors {
      get {
        yield return Tuple0.create();
      }
    }
  }
} // end of namespace _System
namespace Wrappers_Compile {

  public interface _IOption<out T> {
    bool is_None { get; }
    bool is_Some { get; }
    T dtor_value { get; }
    _IOption<__T> DowncastClone<__T>(Func<T, __T> converter0);
    Wrappers_Compile._IResult<T, Dafny.ISequence<char>> ToResult();
    bool IsFailure();
    Wrappers_Compile._IOption<__U> PropagateFailure<__U>();
    T Extract();
  }
  public abstract class Option<T> : _IOption<T> {
    public Option() { }
    public static _IOption<T> Default() {
      return create_None();
    }
    public static Dafny.TypeDescriptor<Wrappers_Compile._IOption<T>> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<Wrappers_Compile._IOption<T>>(Wrappers_Compile.Option<T>.Default());
    }
    public static _IOption<T> create_None() {
      return new Option_None<T>();
    }
    public static _IOption<T> create_Some(T @value) {
      return new Option_Some<T>(@value);
    }
    public bool is_None { get { return this is Option_None<T>; } }
    public bool is_Some { get { return this is Option_Some<T>; } }
    public T dtor_value {
      get {
        var d = this;
        return ((Option_Some<T>)d).@value;
      }
    }
    public abstract _IOption<__T> DowncastClone<__T>(Func<T, __T> converter0);
    public Wrappers_Compile._IResult<T, Dafny.ISequence<char>> ToResult() {
      Wrappers_Compile._IOption<T> _source0 = this;
      if (_source0.is_None) {
        return Wrappers_Compile.Result<T, Dafny.ISequence<char>>.create_Failure(Dafny.Sequence<char>.FromString("Option is None"));
      } else {
        T _0___mcc_h0 = _source0.dtor_value;
        T _1_v = _0___mcc_h0;
        return Wrappers_Compile.Result<T, Dafny.ISequence<char>>.create_Success(_1_v);
      }
    }
    public static T UnwrapOr(Wrappers_Compile._IOption<T> _this, T @default) {
      Wrappers_Compile._IOption<T> _source1 = _this;
      if (_source1.is_None) {
        return @default;
      } else {
        T _2___mcc_h0 = _source1.dtor_value;
        T _3_v = _2___mcc_h0;
        return _3_v;
      }
    }
    public bool IsFailure() {
      return (this).is_None;
    }
    public Wrappers_Compile._IOption<__U> PropagateFailure<__U>() {
      return Wrappers_Compile.Option<__U>.create_None();
    }
    public T Extract() {
      return (this).dtor_value;
    }
  }
  public class Option_None<T> : Option<T> {
    public Option_None() {
    }
    public override _IOption<__T> DowncastClone<__T>(Func<T, __T> converter0) {
      if (this is _IOption<__T> dt) { return dt; }
      return new Option_None<__T>();
    }
    public override bool Equals(object other) {
      var oth = other as Wrappers_Compile.Option_None<T>;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Wrappers_Compile.Option.None";
      return s;
    }
  }
  public class Option_Some<T> : Option<T> {
    public readonly T @value;
    public Option_Some(T @value) {
      this.@value = @value;
    }
    public override _IOption<__T> DowncastClone<__T>(Func<T, __T> converter0) {
      if (this is _IOption<__T> dt) { return dt; }
      return new Option_Some<__T>(converter0(@value));
    }
    public override bool Equals(object other) {
      var oth = other as Wrappers_Compile.Option_Some<T>;
      return oth != null && object.Equals(this.@value, oth.@value);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.@value));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Wrappers_Compile.Option.Some";
      s += "(";
      s += Dafny.Helpers.ToString(this.@value);
      s += ")";
      return s;
    }
  }

  public interface _IResult<out T, out R> {
    bool is_Success { get; }
    bool is_Failure { get; }
    T dtor_value { get; }
    R dtor_error { get; }
    _IResult<__T, __R> DowncastClone<__T, __R>(Func<T, __T> converter0, Func<R, __R> converter1);
    Wrappers_Compile._IOption<T> ToOption();
    bool IsFailure();
    Wrappers_Compile._IResult<__U, R> PropagateFailure<__U>();
    T Extract();
  }
  public abstract class Result<T, R> : _IResult<T, R> {
    public Result() { }
    public static _IResult<T, R> Default(T _default_T) {
      return create_Success(_default_T);
    }
    public static Dafny.TypeDescriptor<Wrappers_Compile._IResult<T, R>> _TypeDescriptor(Dafny.TypeDescriptor<T> _td_T) {
      return new Dafny.TypeDescriptor<Wrappers_Compile._IResult<T, R>>(Wrappers_Compile.Result<T, R>.Default(_td_T.Default()));
    }
    public static _IResult<T, R> create_Success(T @value) {
      return new Result_Success<T, R>(@value);
    }
    public static _IResult<T, R> create_Failure(R error) {
      return new Result_Failure<T, R>(error);
    }
    public bool is_Success { get { return this is Result_Success<T, R>; } }
    public bool is_Failure { get { return this is Result_Failure<T, R>; } }
    public T dtor_value {
      get {
        var d = this;
        return ((Result_Success<T, R>)d).@value;
      }
    }
    public R dtor_error {
      get {
        var d = this;
        return ((Result_Failure<T, R>)d).error;
      }
    }
    public abstract _IResult<__T, __R> DowncastClone<__T, __R>(Func<T, __T> converter0, Func<R, __R> converter1);
    public Wrappers_Compile._IOption<T> ToOption() {
      Wrappers_Compile._IResult<T, R> _source2 = this;
      if (_source2.is_Success) {
        T _4___mcc_h0 = _source2.dtor_value;
        T _5_s = _4___mcc_h0;
        return Wrappers_Compile.Option<T>.create_Some(_5_s);
      } else {
        R _6___mcc_h1 = _source2.dtor_error;
        R _7_e = _6___mcc_h1;
        return Wrappers_Compile.Option<T>.create_None();
      }
    }
    public static T UnwrapOr(Wrappers_Compile._IResult<T, R> _this, T @default) {
      Wrappers_Compile._IResult<T, R> _source3 = _this;
      if (_source3.is_Success) {
        T _8___mcc_h0 = _source3.dtor_value;
        T _9_s = _8___mcc_h0;
        return _9_s;
      } else {
        R _10___mcc_h1 = _source3.dtor_error;
        R _11_e = _10___mcc_h1;
        return @default;
      }
    }
    public bool IsFailure() {
      return (this).is_Failure;
    }
    public Wrappers_Compile._IResult<__U, R> PropagateFailure<__U>() {
      return Wrappers_Compile.Result<__U, R>.create_Failure((this).dtor_error);
    }
    public static Wrappers_Compile._IResult<T, __NewR> MapFailure<__NewR>(Wrappers_Compile._IResult<T, R> _this, Func<R, __NewR> reWrap) {
      Wrappers_Compile._IResult<T, R> _source4 = _this;
      if (_source4.is_Success) {
        T _12___mcc_h0 = _source4.dtor_value;
        T _13_s = _12___mcc_h0;
        return Wrappers_Compile.Result<T, __NewR>.create_Success(_13_s);
      } else {
        R _14___mcc_h1 = _source4.dtor_error;
        R _15_e = _14___mcc_h1;
        return Wrappers_Compile.Result<T, __NewR>.create_Failure(Dafny.Helpers.Id<Func<R, __NewR>>(reWrap)(_15_e));
      }
    }
    public T Extract() {
      return (this).dtor_value;
    }
  }
  public class Result_Success<T, R> : Result<T, R> {
    public readonly T @value;
    public Result_Success(T @value) {
      this.@value = @value;
    }
    public override _IResult<__T, __R> DowncastClone<__T, __R>(Func<T, __T> converter0, Func<R, __R> converter1) {
      if (this is _IResult<__T, __R> dt) { return dt; }
      return new Result_Success<__T, __R>(converter0(@value));
    }
    public override bool Equals(object other) {
      var oth = other as Wrappers_Compile.Result_Success<T, R>;
      return oth != null && object.Equals(this.@value, oth.@value);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.@value));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Wrappers_Compile.Result.Success";
      s += "(";
      s += Dafny.Helpers.ToString(this.@value);
      s += ")";
      return s;
    }
  }
  public class Result_Failure<T, R> : Result<T, R> {
    public readonly R error;
    public Result_Failure(R error) {
      this.error = error;
    }
    public override _IResult<__T, __R> DowncastClone<__T, __R>(Func<T, __T> converter0, Func<R, __R> converter1) {
      if (this is _IResult<__T, __R> dt) { return dt; }
      return new Result_Failure<__T, __R>(converter1(error));
    }
    public override bool Equals(object other) {
      var oth = other as Wrappers_Compile.Result_Failure<T, R>;
      return oth != null && object.Equals(this.error, oth.error);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.error));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Wrappers_Compile.Result.Failure";
      s += "(";
      s += Dafny.Helpers.ToString(this.error);
      s += ")";
      return s;
    }
  }

  public interface _IOutcome<E> {
    bool is_Pass { get; }
    bool is_Fail { get; }
    E dtor_error { get; }
    _IOutcome<__E> DowncastClone<__E>(Func<E, __E> converter0);
    bool IsFailure();
    Wrappers_Compile._IResult<__U, E> PropagateFailure<__U>();
  }
  public abstract class Outcome<E> : _IOutcome<E> {
    public Outcome() { }
    public static _IOutcome<E> Default() {
      return create_Pass();
    }
    public static Dafny.TypeDescriptor<Wrappers_Compile._IOutcome<E>> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<Wrappers_Compile._IOutcome<E>>(Wrappers_Compile.Outcome<E>.Default());
    }
    public static _IOutcome<E> create_Pass() {
      return new Outcome_Pass<E>();
    }
    public static _IOutcome<E> create_Fail(E error) {
      return new Outcome_Fail<E>(error);
    }
    public bool is_Pass { get { return this is Outcome_Pass<E>; } }
    public bool is_Fail { get { return this is Outcome_Fail<E>; } }
    public E dtor_error {
      get {
        var d = this;
        return ((Outcome_Fail<E>)d).error;
      }
    }
    public abstract _IOutcome<__E> DowncastClone<__E>(Func<E, __E> converter0);
    public bool IsFailure() {
      return (this).is_Fail;
    }
    public Wrappers_Compile._IResult<__U, E> PropagateFailure<__U>() {
      return Wrappers_Compile.Result<__U, E>.create_Failure((this).dtor_error);
    }
  }
  public class Outcome_Pass<E> : Outcome<E> {
    public Outcome_Pass() {
    }
    public override _IOutcome<__E> DowncastClone<__E>(Func<E, __E> converter0) {
      if (this is _IOutcome<__E> dt) { return dt; }
      return new Outcome_Pass<__E>();
    }
    public override bool Equals(object other) {
      var oth = other as Wrappers_Compile.Outcome_Pass<E>;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Wrappers_Compile.Outcome.Pass";
      return s;
    }
  }
  public class Outcome_Fail<E> : Outcome<E> {
    public readonly E error;
    public Outcome_Fail(E error) {
      this.error = error;
    }
    public override _IOutcome<__E> DowncastClone<__E>(Func<E, __E> converter0) {
      if (this is _IOutcome<__E> dt) { return dt; }
      return new Outcome_Fail<__E>(converter0(error));
    }
    public override bool Equals(object other) {
      var oth = other as Wrappers_Compile.Outcome_Fail<E>;
      return oth != null && object.Equals(this.error, oth.error);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.error));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Wrappers_Compile.Outcome.Fail";
      s += "(";
      s += Dafny.Helpers.ToString(this.error);
      s += ")";
      return s;
    }
  }

  public partial class __default {
    public static Wrappers_Compile._IOutcome<__E> Need<__E>(bool condition, __E error)
    {
      if (condition) {
        return Wrappers_Compile.Outcome<__E>.create_Pass();
      } else {
        return Wrappers_Compile.Outcome<__E>.create_Fail(error);
      }
    }
  }
} // end of namespace Wrappers_Compile
namespace StandardLibrary_mUInt_Compile {

  public partial class uint8 {
    public static System.Collections.Generic.IEnumerable<byte> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (byte)j; }
    }
    private static readonly Dafny.TypeDescriptor<byte> _TYPE = new Dafny.TypeDescriptor<byte>(0);
    public static Dafny.TypeDescriptor<byte> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class uint16 {
    public static System.Collections.Generic.IEnumerable<ushort> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (ushort)j; }
    }
    private static readonly Dafny.TypeDescriptor<ushort> _TYPE = new Dafny.TypeDescriptor<ushort>(0);
    public static Dafny.TypeDescriptor<ushort> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class uint32 {
    public static System.Collections.Generic.IEnumerable<uint> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (uint)j; }
    }
    private static readonly Dafny.TypeDescriptor<uint> _TYPE = new Dafny.TypeDescriptor<uint>(0);
    public static Dafny.TypeDescriptor<uint> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class uint64 {
    public static System.Collections.Generic.IEnumerable<ulong> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (ulong)j; }
    }
    private static readonly Dafny.TypeDescriptor<ulong> _TYPE = new Dafny.TypeDescriptor<ulong>(0);
    public static Dafny.TypeDescriptor<ulong> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class int32 {
    public static System.Collections.Generic.IEnumerable<int> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (int)j; }
    }
    private static readonly Dafny.TypeDescriptor<int> _TYPE = new Dafny.TypeDescriptor<int>(0);
    public static Dafny.TypeDescriptor<int> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class int64 {
    public static System.Collections.Generic.IEnumerable<long> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (long)j; }
    }
    private static readonly Dafny.TypeDescriptor<long> _TYPE = new Dafny.TypeDescriptor<long>(0);
    public static Dafny.TypeDescriptor<long> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class posInt64 {
    public static System.Collections.Generic.IEnumerable<ulong> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (ulong)j; }
    }
    public static readonly ulong Witness = (ulong)(BigInteger.One);
    private static readonly Dafny.TypeDescriptor<ulong> _TYPE = new Dafny.TypeDescriptor<ulong>(StandardLibrary_mUInt_Compile.posInt64.Witness);
    public static Dafny.TypeDescriptor<ulong> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class seq16<T> {
    public static Dafny.TypeDescriptor<Dafny.ISequence<T>> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<Dafny.ISequence<T>>(Dafny.Sequence<T>.Empty);
    }
  }

  public partial class seq32<T> {
    public static Dafny.TypeDescriptor<Dafny.ISequence<T>> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<Dafny.ISequence<T>>(Dafny.Sequence<T>.Empty);
    }
  }

  public partial class seq64<T> {
    public static Dafny.TypeDescriptor<Dafny.ISequence<T>> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<Dafny.ISequence<T>>(Dafny.Sequence<T>.Empty);
    }
  }

  public partial class __default {
    public static bool UInt8Less(byte a, byte b)
    {
      return (a) < (b);
    }
    public static bool HasUint16Len<__T>(Dafny.ISequence<__T> s) {
      return (new BigInteger((s).Count)) < (StandardLibrary_mUInt_Compile.__default.UINT16__LIMIT);
    }
    public static bool HasUint32Len<__T>(Dafny.ISequence<__T> s) {
      return (new BigInteger((s).Count)) < (StandardLibrary_mUInt_Compile.__default.UINT32__LIMIT);
    }
    public static bool HasUint64Len<__T>(Dafny.ISequence<__T> s) {
      return (new BigInteger((s).Count)) < (StandardLibrary_mUInt_Compile.__default.UINT64__LIMIT);
    }
    public static Dafny.ISequence<byte> UInt16ToSeq(ushort x) {
      byte _16_b0 = (byte)((ushort)((x) / (256)));
      byte _17_b1 = (byte)((ushort)((x) % (256)));
      return Dafny.Sequence<byte>.FromElements(_16_b0, _17_b1);
    }
    public static ushort SeqToUInt16(Dafny.ISequence<byte> s) {
      ushort _18_x0 = (ushort)(((ushort)((s).Select(BigInteger.Zero))) * (256));
      return (ushort)((_18_x0) + ((ushort)((s).Select(BigInteger.One))));
    }
    public static Dafny.ISequence<byte> UInt32ToSeq(uint x) {
      byte _19_b0 = (byte)((x) / (16777216U));
      uint _20_x0 = (x) - (((uint)(_19_b0)) * (16777216U));
      byte _21_b1 = (byte)((_20_x0) / (65536U));
      uint _22_x1 = (_20_x0) - (((uint)(_21_b1)) * (65536U));
      byte _23_b2 = (byte)((_22_x1) / (256U));
      byte _24_b3 = (byte)((_22_x1) % (256U));
      return Dafny.Sequence<byte>.FromElements(_19_b0, _21_b1, _23_b2, _24_b3);
    }
    public static uint SeqToUInt32(Dafny.ISequence<byte> s) {
      uint _25_x0 = ((uint)((s).Select(BigInteger.Zero))) * (16777216U);
      uint _26_x1 = (_25_x0) + (((uint)((s).Select(BigInteger.One))) * (65536U));
      uint _27_x2 = (_26_x1) + (((uint)((s).Select(new BigInteger(2)))) * (256U));
      return (_27_x2) + ((uint)((s).Select(new BigInteger(3))));
    }
    public static Dafny.ISequence<byte> UInt64ToSeq(ulong x) {
      byte _28_b0 = (byte)((x) / (72057594037927936UL));
      ulong _29_x0 = (x) - (((ulong)(_28_b0)) * (72057594037927936UL));
      byte _30_b1 = (byte)((_29_x0) / (281474976710656UL));
      ulong _31_x1 = (_29_x0) - (((ulong)(_30_b1)) * (281474976710656UL));
      byte _32_b2 = (byte)((_31_x1) / (1099511627776UL));
      ulong _33_x2 = (_31_x1) - (((ulong)(_32_b2)) * (1099511627776UL));
      byte _34_b3 = (byte)((_33_x2) / (4294967296UL));
      ulong _35_x3 = (_33_x2) - (((ulong)(_34_b3)) * (4294967296UL));
      byte _36_b4 = (byte)((_35_x3) / (16777216UL));
      ulong _37_x4 = (_35_x3) - (((ulong)(_36_b4)) * (16777216UL));
      byte _38_b5 = (byte)((_37_x4) / (65536UL));
      ulong _39_x5 = (_37_x4) - (((ulong)(_38_b5)) * (65536UL));
      byte _40_b6 = (byte)((_39_x5) / (256UL));
      byte _41_b7 = (byte)((_39_x5) % (256UL));
      return Dafny.Sequence<byte>.FromElements(_28_b0, _30_b1, _32_b2, _34_b3, _36_b4, _38_b5, _40_b6, _41_b7);
    }
    public static ulong SeqToUInt64(Dafny.ISequence<byte> s) {
      ulong _42_x0 = ((ulong)((s).Select(BigInteger.Zero))) * (72057594037927936UL);
      ulong _43_x1 = (_42_x0) + (((ulong)((s).Select(BigInteger.One))) * (281474976710656UL));
      ulong _44_x2 = (_43_x1) + (((ulong)((s).Select(new BigInteger(2)))) * (1099511627776UL));
      ulong _45_x3 = (_44_x2) + (((ulong)((s).Select(new BigInteger(3)))) * (4294967296UL));
      ulong _46_x4 = (_45_x3) + (((ulong)((s).Select(new BigInteger(4)))) * (16777216UL));
      ulong _47_x5 = (_46_x4) + (((ulong)((s).Select(new BigInteger(5)))) * (65536UL));
      ulong _48_x6 = (_47_x5) + (((ulong)((s).Select(new BigInteger(6)))) * (256UL));
      ulong _49_x = (_48_x6) + ((ulong)((s).Select(new BigInteger(7))));
      return _49_x;
    }
    public static BigInteger UINT16__LIMIT { get {
      return new BigInteger(65536);
    } }
    public static BigInteger UINT32__LIMIT { get {
      return new BigInteger(4294967296L);
    } }
    public static BigInteger UINT64__LIMIT { get {
      return BigInteger.Parse("18446744073709551616");
    } }
    public static BigInteger INT32__MAX__LIMIT { get {
      return new BigInteger(2147483648L);
    } }
    public static BigInteger INT64__MAX__LIMIT { get {
      return new BigInteger(9223372036854775808UL);
    } }
  }
} // end of namespace StandardLibrary_mUInt_Compile
namespace StandardLibrary_Compile {

  public partial class __default {
    public static Dafny.ISequence<__T> Join<__T>(Dafny.ISequence<Dafny.ISequence<__T>> ss, Dafny.ISequence<__T> joiner)
    {
      Dafny.ISequence<__T> _50___accumulator = Dafny.Sequence<__T>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((ss).Count)) == (BigInteger.One)) {
        return Dafny.Sequence<__T>.Concat(_50___accumulator, (ss).Select(BigInteger.Zero));
      } else {
        _50___accumulator = Dafny.Sequence<__T>.Concat(_50___accumulator, Dafny.Sequence<__T>.Concat((ss).Select(BigInteger.Zero), joiner));
        Dafny.ISequence<Dafny.ISequence<__T>> _in0 = (ss).Drop(BigInteger.One);
        Dafny.ISequence<__T> _in1 = joiner;
        ss = _in0;
        joiner = _in1;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<Dafny.ISequence<__T>> Split<__T>(Dafny.ISequence<__T> s, __T delim)
    {
      Dafny.ISequence<Dafny.ISequence<__T>> _51___accumulator = Dafny.Sequence<Dafny.ISequence<__T>>.FromElements();
    TAIL_CALL_START: ;
      Wrappers_Compile._IOption<BigInteger> _52_i = StandardLibrary_Compile.__default.FindIndexMatching<__T>(s, delim, BigInteger.Zero);
      if ((_52_i).is_Some) {
        _51___accumulator = Dafny.Sequence<Dafny.ISequence<__T>>.Concat(_51___accumulator, Dafny.Sequence<Dafny.ISequence<__T>>.FromElements((s).Take((_52_i).dtor_value)));
        Dafny.ISequence<__T> _in2 = (s).Drop(((_52_i).dtor_value) + (BigInteger.One));
        __T _in3 = delim;
        s = _in2;
        delim = _in3;
        goto TAIL_CALL_START;
      } else {
        return Dafny.Sequence<Dafny.ISequence<__T>>.Concat(_51___accumulator, Dafny.Sequence<Dafny.ISequence<__T>>.FromElements(s));
      }
    }
    public static Wrappers_Compile._IOption<BigInteger> FindIndexMatching<__T>(Dafny.ISequence<__T> s, __T c, BigInteger i)
    {
      return StandardLibrary_Compile.__default.FindIndex<__T>(s, Dafny.Helpers.Id<Func<__T, Func<__T, bool>>>((_53_c) => ((System.Func<__T, bool>)((_54_x) => {
        return object.Equals(_54_x, _53_c);
      })))(c), i);
    }
    public static Wrappers_Compile._IOption<BigInteger> FindIndex<__T>(Dafny.ISequence<__T> s, Func<__T, bool> f, BigInteger i)
    {
    TAIL_CALL_START: ;
      if ((i) == (new BigInteger((s).Count))) {
        return Wrappers_Compile.Option<BigInteger>.create_None();
      } else if (Dafny.Helpers.Id<Func<__T, bool>>(f)((s).Select(i))) {
        return Wrappers_Compile.Option<BigInteger>.create_Some(i);
      } else {
        Dafny.ISequence<__T> _in4 = s;
        Func<__T, bool> _in5 = f;
        BigInteger _in6 = (i) + (BigInteger.One);
        s = _in4;
        f = _in5;
        i = _in6;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<__T> Filter<__T>(Dafny.ISequence<__T> s, Func<__T, bool> f)
    {
      Dafny.ISequence<__T> _55___accumulator = Dafny.Sequence<__T>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((s).Count)).Sign == 0) {
        return Dafny.Sequence<__T>.Concat(_55___accumulator, Dafny.Sequence<__T>.FromElements());
      } else if (Dafny.Helpers.Id<Func<__T, bool>>(f)((s).Select(BigInteger.Zero))) {
        _55___accumulator = Dafny.Sequence<__T>.Concat(_55___accumulator, Dafny.Sequence<__T>.FromElements((s).Select(BigInteger.Zero)));
        Dafny.ISequence<__T> _in7 = (s).Drop(BigInteger.One);
        Func<__T, bool> _in8 = f;
        s = _in7;
        f = _in8;
        goto TAIL_CALL_START;
      } else {
        Dafny.ISequence<__T> _in9 = (s).Drop(BigInteger.One);
        Func<__T, bool> _in10 = f;
        s = _in9;
        f = _in10;
        goto TAIL_CALL_START;
      }
    }
    public static BigInteger Min(BigInteger a, BigInteger b)
    {
      if ((a) < (b)) {
        return a;
      } else {
        return b;
      }
    }
    public static Dafny.ISequence<__T> Fill<__T>(__T @value, BigInteger n)
    {
      return ((System.Func<Dafny.ISequence<__T>>) (() => {
        BigInteger dim0 = n;
        var arr0 = new __T[Dafny.Helpers.ToIntChecked(dim0,"C# array size must not be larger than max 32-bit int")];
        for (int i0 = 0; i0 < dim0; i0++) {
          var _56___v0 = (BigInteger) i0;
          arr0[(int)(_56___v0)] = @value;
        }
        return Dafny.Sequence<__T>.FromArray(arr0);
      }))();
    }
    public static __T[] SeqToArray<__T>(Dafny.ISequence<__T> s)
    {
      __T[] a = new __T[0];
      __T[] _nw0 = new __T[Dafny.Helpers.ToIntChecked(Dafny.Helpers.ToIntChecked(new BigInteger((s).Count), "C# arrays may not be larger than the max 32-bit integer"),"C# array size must not be larger than max 32-bit int")];
      Func<BigInteger, __T> _arrayinit0 = Dafny.Helpers.Id<Func<Dafny.ISequence<__T>, Func<BigInteger, __T>>>((_57_s) => ((System.Func<BigInteger, __T>)((_58_i) => {
        return (_57_s).Select(_58_i);
      })))(s);
      for (var _arrayinit_00 = 0; _arrayinit_00 < new BigInteger(_nw0.Length); _arrayinit_00++) {
        _nw0[(int)(_arrayinit_00)] = _arrayinit0(_arrayinit_00);
      }
      a = _nw0;
      return a;
    }
    public static bool LexicographicLessOrEqual<__T>(Dafny.ISequence<__T> a, Dafny.ISequence<__T> b, Func<__T, __T, bool> less)
    {
      return Dafny.Helpers.Id<Func<Dafny.ISequence<__T>, Dafny.ISequence<__T>, Func<__T, __T, bool>, bool>>((_59_a, _60_b, _61_less) => Dafny.Helpers.Quantifier<BigInteger>(Dafny.Helpers.IntegerRange(BigInteger.Zero, (new BigInteger((_59_a).Count)) + (BigInteger.One)), false, (((_exists_var_0) => {
        BigInteger _62_k = (BigInteger)_exists_var_0;
        return (((_62_k).Sign != -1) && ((_62_k) <= (new BigInteger((_59_a).Count)))) && (StandardLibrary_Compile.__default.LexicographicLessOrEqualAux<__T>(_59_a, _60_b, _61_less, _62_k));
      }))))(a, b, less);
    }
    public static bool LexicographicLessOrEqualAux<__T>(Dafny.ISequence<__T> a, Dafny.ISequence<__T> b, Func<__T, __T, bool> less, BigInteger lengthOfCommonPrefix)
    {
      return (((lengthOfCommonPrefix) <= (new BigInteger((b).Count))) && (Dafny.Helpers.Id<Func<BigInteger, Dafny.ISequence<__T>, Dafny.ISequence<__T>, bool>>((_63_lengthOfCommonPrefix, _64_a, _65_b) => Dafny.Helpers.Quantifier<BigInteger>(Dafny.Helpers.IntegerRange(BigInteger.Zero, _63_lengthOfCommonPrefix), true, (((_forall_var_0) => {
        BigInteger _66_i = (BigInteger)_forall_var_0;
        return !(((_66_i).Sign != -1) && ((_66_i) < (_63_lengthOfCommonPrefix))) || (object.Equals((_64_a).Select(_66_i), (_65_b).Select(_66_i)));
      }))))(lengthOfCommonPrefix, a, b))) && (((lengthOfCommonPrefix) == (new BigInteger((a).Count))) || (((lengthOfCommonPrefix) < (new BigInteger((b).Count))) && (Dafny.Helpers.Id<Func<__T, __T, bool>>(less)((a).Select(lengthOfCommonPrefix), (b).Select(lengthOfCommonPrefix)))));
    }
    public static Dafny.ISequence<Dafny.ISequence<__T>> SetToOrderedSequence<__T>(Dafny.ISet<Dafny.ISequence<__T>> s, Func<__T, __T, bool> less)
    {
      Dafny.ISequence<Dafny.ISequence<__T>> _67___accumulator = Dafny.Sequence<Dafny.ISequence<__T>>.FromElements();
    TAIL_CALL_START: ;
      if ((s).Equals((Dafny.Set<Dafny.ISequence<__T>>.FromElements()))) {
        return Dafny.Sequence<Dafny.ISequence<__T>>.Concat(_67___accumulator, Dafny.Sequence<Dafny.ISequence<__T>>.FromElements());
      } else {
        return Dafny.Helpers.Let<int, Dafny.ISequence<Dafny.ISequence<__T>>>(0, _let_dummy_0 =>  {
          Dafny.ISequence<__T> _68_a = Dafny.Sequence<__T>.Empty;
          foreach (Dafny.ISequence<__T> _assign_such_that_0 in (s).Elements) {
            _68_a = (Dafny.ISequence<__T>)_assign_such_that_0;
            if (((s).Contains((_68_a))) && (StandardLibrary_Compile.__default.IsMinimum<__T>(_68_a, s, less))) {
              goto after__ASSIGN_SUCH_THAT_0;
            }
          }
          throw new System.Exception("assign-such-that search produced no value (line 348)");
        after__ASSIGN_SUCH_THAT_0: ;
          return Dafny.Sequence<Dafny.ISequence<__T>>.Concat(Dafny.Sequence<Dafny.ISequence<__T>>.FromElements(_68_a), StandardLibrary_Compile.__default.SetToOrderedSequence<__T>(Dafny.Set<Dafny.ISequence<__T>>.Difference(s, Dafny.Set<Dafny.ISequence<__T>>.FromElements(_68_a)), less));
        }
        );
      }
    }
    public static bool IsMinimum<__T>(Dafny.ISequence<__T> a, Dafny.ISet<Dafny.ISequence<__T>> s, Func<__T, __T, bool> less)
    {
      return ((s).Contains((a))) && (Dafny.Helpers.Id<Func<Dafny.ISet<Dafny.ISequence<__T>>, Dafny.ISequence<__T>, Func<__T, __T, bool>, bool>>((_69_s, _70_a, _71_less) => Dafny.Helpers.Quantifier<Dafny.ISequence<__T>>((_69_s).Elements, true, (((_forall_var_1) => {
        Dafny.ISequence<__T> _72_z = (Dafny.ISequence<__T>)_forall_var_1;
        return !((_69_s).Contains((_72_z))) || (StandardLibrary_Compile.__default.LexicographicLessOrEqual<__T>(_70_a, _72_z, _71_less));
      }))))(s, a, less));
    }
  }
} // end of namespace StandardLibrary_Compile
namespace UTF8 {

  public partial class ValidUTF8Bytes {
    private static readonly Dafny.ISequence<byte> Witness = Dafny.Sequence<byte>.FromElements();
    public static Dafny.ISequence<byte> Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.ISequence<byte>> _TYPE = new Dafny.TypeDescriptor<Dafny.ISequence<byte>>(UTF8.ValidUTF8Bytes.Default());
    public static Dafny.TypeDescriptor<Dafny.ISequence<byte>> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class __default {
    public static bool IsASCIIString(Dafny.ISequence<char> s) {
      return Dafny.Helpers.Id<Func<Dafny.ISequence<char>, bool>>((_73_s) => Dafny.Helpers.Quantifier<BigInteger>(Dafny.Helpers.IntegerRange(BigInteger.Zero, new BigInteger((_73_s).Count)), true, (((_forall_var_2) => {
        BigInteger _74_i = (BigInteger)_forall_var_2;
        return !(((_74_i).Sign != -1) && ((_74_i) < (new BigInteger((_73_s).Count)))) || ((new BigInteger((_73_s).Select(_74_i))) < (new BigInteger(128)));
      }))))(s);
    }
    public static bool Uses1Byte(Dafny.ISequence<byte> s) {
      return ((0) <= ((s).Select(BigInteger.Zero))) && (((s).Select(BigInteger.Zero)) <= (127));
    }
    public static bool Uses2Bytes(Dafny.ISequence<byte> s) {
      return (((194) <= ((s).Select(BigInteger.Zero))) && (((s).Select(BigInteger.Zero)) <= (223))) && (((128) <= ((s).Select(BigInteger.One))) && (((s).Select(BigInteger.One)) <= (191)));
    }
    public static bool Uses3Bytes(Dafny.ISequence<byte> s) {
      return (((((((s).Select(BigInteger.Zero)) == (224)) && (((160) <= ((s).Select(BigInteger.One))) && (((s).Select(BigInteger.One)) <= (191)))) && (((128) <= ((s).Select(new BigInteger(2)))) && (((s).Select(new BigInteger(2))) <= (191)))) || (((((225) <= ((s).Select(BigInteger.Zero))) && (((s).Select(BigInteger.Zero)) <= (236))) && (((128) <= ((s).Select(BigInteger.One))) && (((s).Select(BigInteger.One)) <= (191)))) && (((128) <= ((s).Select(new BigInteger(2)))) && (((s).Select(new BigInteger(2))) <= (191))))) || (((((s).Select(BigInteger.Zero)) == (237)) && (((128) <= ((s).Select(BigInteger.One))) && (((s).Select(BigInteger.One)) <= (159)))) && (((128) <= ((s).Select(new BigInteger(2)))) && (((s).Select(new BigInteger(2))) <= (191))))) || (((((238) <= ((s).Select(BigInteger.Zero))) && (((s).Select(BigInteger.Zero)) <= (239))) && (((128) <= ((s).Select(BigInteger.One))) && (((s).Select(BigInteger.One)) <= (191)))) && (((128) <= ((s).Select(new BigInteger(2)))) && (((s).Select(new BigInteger(2))) <= (191))));
    }
    public static bool Uses4Bytes(Dafny.ISequence<byte> s) {
      return (((((((s).Select(BigInteger.Zero)) == (240)) && (((144) <= ((s).Select(BigInteger.One))) && (((s).Select(BigInteger.One)) <= (191)))) && (((128) <= ((s).Select(new BigInteger(2)))) && (((s).Select(new BigInteger(2))) <= (191)))) && (((128) <= ((s).Select(new BigInteger(3)))) && (((s).Select(new BigInteger(3))) <= (191)))) || ((((((241) <= ((s).Select(BigInteger.Zero))) && (((s).Select(BigInteger.Zero)) <= (243))) && (((128) <= ((s).Select(BigInteger.One))) && (((s).Select(BigInteger.One)) <= (191)))) && (((128) <= ((s).Select(new BigInteger(2)))) && (((s).Select(new BigInteger(2))) <= (191)))) && (((128) <= ((s).Select(new BigInteger(3)))) && (((s).Select(new BigInteger(3))) <= (191))))) || ((((((s).Select(BigInteger.Zero)) == (244)) && (((128) <= ((s).Select(BigInteger.One))) && (((s).Select(BigInteger.One)) <= (143)))) && (((128) <= ((s).Select(new BigInteger(2)))) && (((s).Select(new BigInteger(2))) <= (191)))) && (((128) <= ((s).Select(new BigInteger(3)))) && (((s).Select(new BigInteger(3))) <= (191))));
    }
    public static bool ValidUTF8Range(Dafny.ISequence<byte> a, BigInteger lo, BigInteger hi)
    {
    TAIL_CALL_START: ;
      if ((lo) == (hi)) {
        return true;
      } else {
        Dafny.ISequence<byte> _75_r = (a).Subsequence(lo, hi);
        if (UTF8.__default.Uses1Byte(_75_r)) {
          Dafny.ISequence<byte> _in11 = a;
          BigInteger _in12 = (lo) + (BigInteger.One);
          BigInteger _in13 = hi;
          a = _in11;
          lo = _in12;
          hi = _in13;
          goto TAIL_CALL_START;
        } else if (((new BigInteger(2)) <= (new BigInteger((_75_r).Count))) && (UTF8.__default.Uses2Bytes(_75_r))) {
          Dafny.ISequence<byte> _in14 = a;
          BigInteger _in15 = (lo) + (new BigInteger(2));
          BigInteger _in16 = hi;
          a = _in14;
          lo = _in15;
          hi = _in16;
          goto TAIL_CALL_START;
        } else if (((new BigInteger(3)) <= (new BigInteger((_75_r).Count))) && (UTF8.__default.Uses3Bytes(_75_r))) {
          Dafny.ISequence<byte> _in17 = a;
          BigInteger _in18 = (lo) + (new BigInteger(3));
          BigInteger _in19 = hi;
          a = _in17;
          lo = _in18;
          hi = _in19;
          goto TAIL_CALL_START;
        } else if (((new BigInteger(4)) <= (new BigInteger((_75_r).Count))) && (UTF8.__default.Uses4Bytes(_75_r))) {
          Dafny.ISequence<byte> _in20 = a;
          BigInteger _in21 = (lo) + (new BigInteger(4));
          BigInteger _in22 = hi;
          a = _in20;
          lo = _in21;
          hi = _in22;
          goto TAIL_CALL_START;
        } else {
          return false;
        }
      }
    }
    public static bool ValidUTF8Seq(Dafny.ISequence<byte> s) {
      return UTF8.__default.ValidUTF8Range(s, BigInteger.Zero, new BigInteger((s).Count));
    }
  }
} // end of namespace UTF8
namespace Dafny.Aws.Cryptography.Primitives.Types {

  public interface _IAES__GCM {
    bool is_AES__GCM { get; }
    int dtor_keyLength { get; }
    int dtor_tagLength { get; }
    int dtor_ivLength { get; }
    _IAES__GCM DowncastClone();
  }
  public class AES__GCM : _IAES__GCM {
    public readonly int keyLength;
    public readonly int tagLength;
    public readonly int ivLength;
    public AES__GCM(int keyLength, int tagLength, int ivLength) {
      this.keyLength = keyLength;
      this.tagLength = tagLength;
      this.ivLength = ivLength;
    }
    public _IAES__GCM DowncastClone() {
      if (this is _IAES__GCM dt) { return dt; }
      return new AES__GCM(keyLength, tagLength, ivLength);
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Aws.Cryptography.Primitives.Types.AES__GCM;
      return oth != null && this.keyLength == oth.keyLength && this.tagLength == oth.tagLength && this.ivLength == oth.ivLength;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.keyLength));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.tagLength));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.ivLength));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Aws.Cryptography.Primitives.Types_Compile.AES_GCM.AES_GCM";
      s += "(";
      s += Dafny.Helpers.ToString(this.keyLength);
      s += ", ";
      s += Dafny.Helpers.ToString(this.tagLength);
      s += ", ";
      s += Dafny.Helpers.ToString(this.ivLength);
      s += ")";
      return s;
    }
    private static readonly _IAES__GCM theDefault = create(0, 0, 0);
    public static _IAES__GCM Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.Aws.Cryptography.Primitives.Types._IAES__GCM> _TYPE = new Dafny.TypeDescriptor<Dafny.Aws.Cryptography.Primitives.Types._IAES__GCM>(Dafny.Aws.Cryptography.Primitives.Types.AES__GCM.Default());
    public static Dafny.TypeDescriptor<Dafny.Aws.Cryptography.Primitives.Types._IAES__GCM> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IAES__GCM create(int keyLength, int tagLength, int ivLength) {
      return new AES__GCM(keyLength, tagLength, ivLength);
    }
    public bool is_AES__GCM { get { return true; } }
    public int dtor_keyLength {
      get {
        return this.keyLength;
      }
    }
    public int dtor_tagLength {
      get {
        return this.tagLength;
      }
    }
    public int dtor_ivLength {
      get {
        return this.ivLength;
      }
    }
  }

  public interface _IAESDecryptInput {
    bool is_AESDecryptInput { get; }
    Dafny.Aws.Cryptography.Primitives.Types._IAES__GCM dtor_encAlg { get; }
    Dafny.ISequence<byte> dtor_key { get; }
    Dafny.ISequence<byte> dtor_cipherTxt { get; }
    Dafny.ISequence<byte> dtor_authTag { get; }
    Dafny.ISequence<byte> dtor_iv { get; }
    Dafny.ISequence<byte> dtor_aad { get; }
    _IAESDecryptInput DowncastClone();
  }
  public class AESDecryptInput : _IAESDecryptInput {
    public readonly Dafny.Aws.Cryptography.Primitives.Types._IAES__GCM encAlg;
    public readonly Dafny.ISequence<byte> key;
    public readonly Dafny.ISequence<byte> cipherTxt;
    public readonly Dafny.ISequence<byte> authTag;
    public readonly Dafny.ISequence<byte> iv;
    public readonly Dafny.ISequence<byte> aad;
    public AESDecryptInput(Dafny.Aws.Cryptography.Primitives.Types._IAES__GCM encAlg, Dafny.ISequence<byte> key, Dafny.ISequence<byte> cipherTxt, Dafny.ISequence<byte> authTag, Dafny.ISequence<byte> iv, Dafny.ISequence<byte> aad) {
      this.encAlg = encAlg;
      this.key = key;
      this.cipherTxt = cipherTxt;
      this.authTag = authTag;
      this.iv = iv;
      this.aad = aad;
    }
    public _IAESDecryptInput DowncastClone() {
      if (this is _IAESDecryptInput dt) { return dt; }
      return new AESDecryptInput(encAlg, key, cipherTxt, authTag, iv, aad);
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Aws.Cryptography.Primitives.Types.AESDecryptInput;
      return oth != null && object.Equals(this.encAlg, oth.encAlg) && object.Equals(this.key, oth.key) && object.Equals(this.cipherTxt, oth.cipherTxt) && object.Equals(this.authTag, oth.authTag) && object.Equals(this.iv, oth.iv) && object.Equals(this.aad, oth.aad);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.encAlg));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.key));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.cipherTxt));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.authTag));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.iv));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.aad));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Aws.Cryptography.Primitives.Types_Compile.AESDecryptInput.AESDecryptInput";
      s += "(";
      s += Dafny.Helpers.ToString(this.encAlg);
      s += ", ";
      s += Dafny.Helpers.ToString(this.key);
      s += ", ";
      s += Dafny.Helpers.ToString(this.cipherTxt);
      s += ", ";
      s += Dafny.Helpers.ToString(this.authTag);
      s += ", ";
      s += Dafny.Helpers.ToString(this.iv);
      s += ", ";
      s += Dafny.Helpers.ToString(this.aad);
      s += ")";
      return s;
    }
    private static readonly _IAESDecryptInput theDefault = create(Dafny.Aws.Cryptography.Primitives.Types.AES__GCM.Default(), Dafny.Sequence<byte>.Empty, Dafny.Sequence<byte>.Empty, Dafny.Sequence<byte>.Empty, Dafny.Sequence<byte>.Empty, Dafny.Sequence<byte>.Empty);
    public static _IAESDecryptInput Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.Aws.Cryptography.Primitives.Types._IAESDecryptInput> _TYPE = new Dafny.TypeDescriptor<Dafny.Aws.Cryptography.Primitives.Types._IAESDecryptInput>(Dafny.Aws.Cryptography.Primitives.Types.AESDecryptInput.Default());
    public static Dafny.TypeDescriptor<Dafny.Aws.Cryptography.Primitives.Types._IAESDecryptInput> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IAESDecryptInput create(Dafny.Aws.Cryptography.Primitives.Types._IAES__GCM encAlg, Dafny.ISequence<byte> key, Dafny.ISequence<byte> cipherTxt, Dafny.ISequence<byte> authTag, Dafny.ISequence<byte> iv, Dafny.ISequence<byte> aad) {
      return new AESDecryptInput(encAlg, key, cipherTxt, authTag, iv, aad);
    }
    public bool is_AESDecryptInput { get { return true; } }
    public Dafny.Aws.Cryptography.Primitives.Types._IAES__GCM dtor_encAlg {
      get {
        return this.encAlg;
      }
    }
    public Dafny.ISequence<byte> dtor_key {
      get {
        return this.key;
      }
    }
    public Dafny.ISequence<byte> dtor_cipherTxt {
      get {
        return this.cipherTxt;
      }
    }
    public Dafny.ISequence<byte> dtor_authTag {
      get {
        return this.authTag;
      }
    }
    public Dafny.ISequence<byte> dtor_iv {
      get {
        return this.iv;
      }
    }
    public Dafny.ISequence<byte> dtor_aad {
      get {
        return this.aad;
      }
    }
  }

  public interface _IAESEncryptInput {
    bool is_AESEncryptInput { get; }
    Dafny.Aws.Cryptography.Primitives.Types._IAES__GCM dtor_encAlg { get; }
    Dafny.ISequence<byte> dtor_iv { get; }
    Dafny.ISequence<byte> dtor_key { get; }
    Dafny.ISequence<byte> dtor_msg { get; }
    Dafny.ISequence<byte> dtor_aad { get; }
    _IAESEncryptInput DowncastClone();
  }
  public class AESEncryptInput : _IAESEncryptInput {
    public readonly Dafny.Aws.Cryptography.Primitives.Types._IAES__GCM encAlg;
    public readonly Dafny.ISequence<byte> iv;
    public readonly Dafny.ISequence<byte> key;
    public readonly Dafny.ISequence<byte> msg;
    public readonly Dafny.ISequence<byte> aad;
    public AESEncryptInput(Dafny.Aws.Cryptography.Primitives.Types._IAES__GCM encAlg, Dafny.ISequence<byte> iv, Dafny.ISequence<byte> key, Dafny.ISequence<byte> msg, Dafny.ISequence<byte> aad) {
      this.encAlg = encAlg;
      this.iv = iv;
      this.key = key;
      this.msg = msg;
      this.aad = aad;
    }
    public _IAESEncryptInput DowncastClone() {
      if (this is _IAESEncryptInput dt) { return dt; }
      return new AESEncryptInput(encAlg, iv, key, msg, aad);
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Aws.Cryptography.Primitives.Types.AESEncryptInput;
      return oth != null && object.Equals(this.encAlg, oth.encAlg) && object.Equals(this.iv, oth.iv) && object.Equals(this.key, oth.key) && object.Equals(this.msg, oth.msg) && object.Equals(this.aad, oth.aad);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.encAlg));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.iv));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.key));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.msg));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.aad));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Aws.Cryptography.Primitives.Types_Compile.AESEncryptInput.AESEncryptInput";
      s += "(";
      s += Dafny.Helpers.ToString(this.encAlg);
      s += ", ";
      s += Dafny.Helpers.ToString(this.iv);
      s += ", ";
      s += Dafny.Helpers.ToString(this.key);
      s += ", ";
      s += Dafny.Helpers.ToString(this.msg);
      s += ", ";
      s += Dafny.Helpers.ToString(this.aad);
      s += ")";
      return s;
    }
    private static readonly _IAESEncryptInput theDefault = create(Dafny.Aws.Cryptography.Primitives.Types.AES__GCM.Default(), Dafny.Sequence<byte>.Empty, Dafny.Sequence<byte>.Empty, Dafny.Sequence<byte>.Empty, Dafny.Sequence<byte>.Empty);
    public static _IAESEncryptInput Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.Aws.Cryptography.Primitives.Types._IAESEncryptInput> _TYPE = new Dafny.TypeDescriptor<Dafny.Aws.Cryptography.Primitives.Types._IAESEncryptInput>(Dafny.Aws.Cryptography.Primitives.Types.AESEncryptInput.Default());
    public static Dafny.TypeDescriptor<Dafny.Aws.Cryptography.Primitives.Types._IAESEncryptInput> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IAESEncryptInput create(Dafny.Aws.Cryptography.Primitives.Types._IAES__GCM encAlg, Dafny.ISequence<byte> iv, Dafny.ISequence<byte> key, Dafny.ISequence<byte> msg, Dafny.ISequence<byte> aad) {
      return new AESEncryptInput(encAlg, iv, key, msg, aad);
    }
    public bool is_AESEncryptInput { get { return true; } }
    public Dafny.Aws.Cryptography.Primitives.Types._IAES__GCM dtor_encAlg {
      get {
        return this.encAlg;
      }
    }
    public Dafny.ISequence<byte> dtor_iv {
      get {
        return this.iv;
      }
    }
    public Dafny.ISequence<byte> dtor_key {
      get {
        return this.key;
      }
    }
    public Dafny.ISequence<byte> dtor_msg {
      get {
        return this.msg;
      }
    }
    public Dafny.ISequence<byte> dtor_aad {
      get {
        return this.aad;
      }
    }
  }

  public interface _IAESEncryptOutput {
    bool is_AESEncryptOutput { get; }
    Dafny.ISequence<byte> dtor_cipherText { get; }
    Dafny.ISequence<byte> dtor_authTag { get; }
    _IAESEncryptOutput DowncastClone();
  }
  public class AESEncryptOutput : _IAESEncryptOutput {
    public readonly Dafny.ISequence<byte> cipherText;
    public readonly Dafny.ISequence<byte> authTag;
    public AESEncryptOutput(Dafny.ISequence<byte> cipherText, Dafny.ISequence<byte> authTag) {
      this.cipherText = cipherText;
      this.authTag = authTag;
    }
    public _IAESEncryptOutput DowncastClone() {
      if (this is _IAESEncryptOutput dt) { return dt; }
      return new AESEncryptOutput(cipherText, authTag);
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Aws.Cryptography.Primitives.Types.AESEncryptOutput;
      return oth != null && object.Equals(this.cipherText, oth.cipherText) && object.Equals(this.authTag, oth.authTag);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.cipherText));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.authTag));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Aws.Cryptography.Primitives.Types_Compile.AESEncryptOutput.AESEncryptOutput";
      s += "(";
      s += Dafny.Helpers.ToString(this.cipherText);
      s += ", ";
      s += Dafny.Helpers.ToString(this.authTag);
      s += ")";
      return s;
    }
    private static readonly _IAESEncryptOutput theDefault = create(Dafny.Sequence<byte>.Empty, Dafny.Sequence<byte>.Empty);
    public static _IAESEncryptOutput Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.Aws.Cryptography.Primitives.Types._IAESEncryptOutput> _TYPE = new Dafny.TypeDescriptor<Dafny.Aws.Cryptography.Primitives.Types._IAESEncryptOutput>(Dafny.Aws.Cryptography.Primitives.Types.AESEncryptOutput.Default());
    public static Dafny.TypeDescriptor<Dafny.Aws.Cryptography.Primitives.Types._IAESEncryptOutput> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IAESEncryptOutput create(Dafny.ISequence<byte> cipherText, Dafny.ISequence<byte> authTag) {
      return new AESEncryptOutput(cipherText, authTag);
    }
    public bool is_AESEncryptOutput { get { return true; } }
    public Dafny.ISequence<byte> dtor_cipherText {
      get {
        return this.cipherText;
      }
    }
    public Dafny.ISequence<byte> dtor_authTag {
      get {
        return this.authTag;
      }
    }
  }

  public interface IAwsCryptographicPrimitivesClient {
    Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.Aws.Cryptography.Primitives.Types._IError> GenerateRandomBytes(Dafny.Aws.Cryptography.Primitives.Types._IGenerateRandomBytesInput input);
    Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.Aws.Cryptography.Primitives.Types._IError> Digest(Dafny.Aws.Cryptography.Primitives.Types._IDigestInput input);
    Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.Aws.Cryptography.Primitives.Types._IError> HMac(Dafny.Aws.Cryptography.Primitives.Types._IHMacInput input);
    Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.Aws.Cryptography.Primitives.Types._IError> HkdfExtract(Dafny.Aws.Cryptography.Primitives.Types._IHkdfExtractInput input);
    Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.Aws.Cryptography.Primitives.Types._IError> HkdfExpand(Dafny.Aws.Cryptography.Primitives.Types._IHkdfExpandInput input);
    Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.Aws.Cryptography.Primitives.Types._IError> Hkdf(Dafny.Aws.Cryptography.Primitives.Types._IHkdfInput input);
    Wrappers_Compile._IResult<Dafny.Aws.Cryptography.Primitives.Types._IAESEncryptOutput, Dafny.Aws.Cryptography.Primitives.Types._IError> AESEncrypt(Dafny.Aws.Cryptography.Primitives.Types._IAESEncryptInput input);
    Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.Aws.Cryptography.Primitives.Types._IError> AESDecrypt(Dafny.Aws.Cryptography.Primitives.Types._IAESDecryptInput input);
  }
  public class _Companion_IAwsCryptographicPrimitivesClient {
  }

  public interface _ICryptoConfig {
    bool is_CryptoConfig { get; }
    _ICryptoConfig DowncastClone();
  }
  public class CryptoConfig : _ICryptoConfig {
    public CryptoConfig() {
    }
    public _ICryptoConfig DowncastClone() {
      if (this is _ICryptoConfig dt) { return dt; }
      return new CryptoConfig();
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Aws.Cryptography.Primitives.Types.CryptoConfig;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Aws.Cryptography.Primitives.Types_Compile.CryptoConfig.CryptoConfig";
      return s;
    }
    private static readonly _ICryptoConfig theDefault = create();
    public static _ICryptoConfig Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.Aws.Cryptography.Primitives.Types._ICryptoConfig> _TYPE = new Dafny.TypeDescriptor<Dafny.Aws.Cryptography.Primitives.Types._ICryptoConfig>(Dafny.Aws.Cryptography.Primitives.Types.CryptoConfig.Default());
    public static Dafny.TypeDescriptor<Dafny.Aws.Cryptography.Primitives.Types._ICryptoConfig> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ICryptoConfig create() {
      return new CryptoConfig();
    }
    public bool is_CryptoConfig { get { return true; } }
    public static System.Collections.Generic.IEnumerable<_ICryptoConfig> AllSingletonConstructors {
      get {
        yield return CryptoConfig.create();
      }
    }
  }

  public interface _IDigestAlgorithm {
    bool is_SHA__512 { get; }
    bool is_SHA__384 { get; }
    bool is_SHA__256 { get; }
    _IDigestAlgorithm DowncastClone();
  }
  public abstract class DigestAlgorithm : _IDigestAlgorithm {
    public DigestAlgorithm() { }
    private static readonly _IDigestAlgorithm theDefault = create_SHA__512();
    public static _IDigestAlgorithm Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.Aws.Cryptography.Primitives.Types._IDigestAlgorithm> _TYPE = new Dafny.TypeDescriptor<Dafny.Aws.Cryptography.Primitives.Types._IDigestAlgorithm>(Dafny.Aws.Cryptography.Primitives.Types.DigestAlgorithm.Default());
    public static Dafny.TypeDescriptor<Dafny.Aws.Cryptography.Primitives.Types._IDigestAlgorithm> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IDigestAlgorithm create_SHA__512() {
      return new DigestAlgorithm_SHA__512();
    }
    public static _IDigestAlgorithm create_SHA__384() {
      return new DigestAlgorithm_SHA__384();
    }
    public static _IDigestAlgorithm create_SHA__256() {
      return new DigestAlgorithm_SHA__256();
    }
    public bool is_SHA__512 { get { return this is DigestAlgorithm_SHA__512; } }
    public bool is_SHA__384 { get { return this is DigestAlgorithm_SHA__384; } }
    public bool is_SHA__256 { get { return this is DigestAlgorithm_SHA__256; } }
    public static System.Collections.Generic.IEnumerable<_IDigestAlgorithm> AllSingletonConstructors {
      get {
        yield return DigestAlgorithm.create_SHA__512();
        yield return DigestAlgorithm.create_SHA__384();
        yield return DigestAlgorithm.create_SHA__256();
      }
    }
    public abstract _IDigestAlgorithm DowncastClone();
  }
  public class DigestAlgorithm_SHA__512 : DigestAlgorithm {
    public DigestAlgorithm_SHA__512() {
    }
    public override _IDigestAlgorithm DowncastClone() {
      if (this is _IDigestAlgorithm dt) { return dt; }
      return new DigestAlgorithm_SHA__512();
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Aws.Cryptography.Primitives.Types.DigestAlgorithm_SHA__512;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Aws.Cryptography.Primitives.Types_Compile.DigestAlgorithm.SHA_512";
      return s;
    }
  }
  public class DigestAlgorithm_SHA__384 : DigestAlgorithm {
    public DigestAlgorithm_SHA__384() {
    }
    public override _IDigestAlgorithm DowncastClone() {
      if (this is _IDigestAlgorithm dt) { return dt; }
      return new DigestAlgorithm_SHA__384();
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Aws.Cryptography.Primitives.Types.DigestAlgorithm_SHA__384;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Aws.Cryptography.Primitives.Types_Compile.DigestAlgorithm.SHA_384";
      return s;
    }
  }
  public class DigestAlgorithm_SHA__256 : DigestAlgorithm {
    public DigestAlgorithm_SHA__256() {
    }
    public override _IDigestAlgorithm DowncastClone() {
      if (this is _IDigestAlgorithm dt) { return dt; }
      return new DigestAlgorithm_SHA__256();
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Aws.Cryptography.Primitives.Types.DigestAlgorithm_SHA__256;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Aws.Cryptography.Primitives.Types_Compile.DigestAlgorithm.SHA_256";
      return s;
    }
  }

  public interface _IDigestInput {
    bool is_DigestInput { get; }
    Dafny.Aws.Cryptography.Primitives.Types._IDigestAlgorithm dtor_digestAlgorithm { get; }
    Dafny.ISequence<byte> dtor_message { get; }
    _IDigestInput DowncastClone();
  }
  public class DigestInput : _IDigestInput {
    public readonly Dafny.Aws.Cryptography.Primitives.Types._IDigestAlgorithm digestAlgorithm;
    public readonly Dafny.ISequence<byte> message;
    public DigestInput(Dafny.Aws.Cryptography.Primitives.Types._IDigestAlgorithm digestAlgorithm, Dafny.ISequence<byte> message) {
      this.digestAlgorithm = digestAlgorithm;
      this.message = message;
    }
    public _IDigestInput DowncastClone() {
      if (this is _IDigestInput dt) { return dt; }
      return new DigestInput(digestAlgorithm, message);
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Aws.Cryptography.Primitives.Types.DigestInput;
      return oth != null && object.Equals(this.digestAlgorithm, oth.digestAlgorithm) && object.Equals(this.message, oth.message);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.digestAlgorithm));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.message));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Aws.Cryptography.Primitives.Types_Compile.DigestInput.DigestInput";
      s += "(";
      s += Dafny.Helpers.ToString(this.digestAlgorithm);
      s += ", ";
      s += Dafny.Helpers.ToString(this.message);
      s += ")";
      return s;
    }
    private static readonly _IDigestInput theDefault = create(Dafny.Aws.Cryptography.Primitives.Types.DigestAlgorithm.Default(), Dafny.Sequence<byte>.Empty);
    public static _IDigestInput Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.Aws.Cryptography.Primitives.Types._IDigestInput> _TYPE = new Dafny.TypeDescriptor<Dafny.Aws.Cryptography.Primitives.Types._IDigestInput>(Dafny.Aws.Cryptography.Primitives.Types.DigestInput.Default());
    public static Dafny.TypeDescriptor<Dafny.Aws.Cryptography.Primitives.Types._IDigestInput> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IDigestInput create(Dafny.Aws.Cryptography.Primitives.Types._IDigestAlgorithm digestAlgorithm, Dafny.ISequence<byte> message) {
      return new DigestInput(digestAlgorithm, message);
    }
    public bool is_DigestInput { get { return true; } }
    public Dafny.Aws.Cryptography.Primitives.Types._IDigestAlgorithm dtor_digestAlgorithm {
      get {
        return this.digestAlgorithm;
      }
    }
    public Dafny.ISequence<byte> dtor_message {
      get {
        return this.message;
      }
    }
  }

  public interface _IGenerateRandomBytesInput {
    bool is_GenerateRandomBytesInput { get; }
    int dtor_length { get; }
    _IGenerateRandomBytesInput DowncastClone();
  }
  public class GenerateRandomBytesInput : _IGenerateRandomBytesInput {
    public readonly int length;
    public GenerateRandomBytesInput(int length) {
      this.length = length;
    }
    public _IGenerateRandomBytesInput DowncastClone() {
      if (this is _IGenerateRandomBytesInput dt) { return dt; }
      return new GenerateRandomBytesInput(length);
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Aws.Cryptography.Primitives.Types.GenerateRandomBytesInput;
      return oth != null && this.length == oth.length;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.length));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Aws.Cryptography.Primitives.Types_Compile.GenerateRandomBytesInput.GenerateRandomBytesInput";
      s += "(";
      s += Dafny.Helpers.ToString(this.length);
      s += ")";
      return s;
    }
    private static readonly _IGenerateRandomBytesInput theDefault = create(0);
    public static _IGenerateRandomBytesInput Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.Aws.Cryptography.Primitives.Types._IGenerateRandomBytesInput> _TYPE = new Dafny.TypeDescriptor<Dafny.Aws.Cryptography.Primitives.Types._IGenerateRandomBytesInput>(Dafny.Aws.Cryptography.Primitives.Types.GenerateRandomBytesInput.Default());
    public static Dafny.TypeDescriptor<Dafny.Aws.Cryptography.Primitives.Types._IGenerateRandomBytesInput> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IGenerateRandomBytesInput create(int length) {
      return new GenerateRandomBytesInput(length);
    }
    public bool is_GenerateRandomBytesInput { get { return true; } }
    public int dtor_length {
      get {
        return this.length;
      }
    }
  }

  public interface _IHkdfExpandInput {
    bool is_HkdfExpandInput { get; }
    Dafny.Aws.Cryptography.Primitives.Types._IDigestAlgorithm dtor_digestAlgorithm { get; }
    Dafny.ISequence<byte> dtor_prk { get; }
    Dafny.ISequence<byte> dtor_info { get; }
    int dtor_expectedLength { get; }
    _IHkdfExpandInput DowncastClone();
  }
  public class HkdfExpandInput : _IHkdfExpandInput {
    public readonly Dafny.Aws.Cryptography.Primitives.Types._IDigestAlgorithm digestAlgorithm;
    public readonly Dafny.ISequence<byte> prk;
    public readonly Dafny.ISequence<byte> info;
    public readonly int expectedLength;
    public HkdfExpandInput(Dafny.Aws.Cryptography.Primitives.Types._IDigestAlgorithm digestAlgorithm, Dafny.ISequence<byte> prk, Dafny.ISequence<byte> info, int expectedLength) {
      this.digestAlgorithm = digestAlgorithm;
      this.prk = prk;
      this.info = info;
      this.expectedLength = expectedLength;
    }
    public _IHkdfExpandInput DowncastClone() {
      if (this is _IHkdfExpandInput dt) { return dt; }
      return new HkdfExpandInput(digestAlgorithm, prk, info, expectedLength);
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Aws.Cryptography.Primitives.Types.HkdfExpandInput;
      return oth != null && object.Equals(this.digestAlgorithm, oth.digestAlgorithm) && object.Equals(this.prk, oth.prk) && object.Equals(this.info, oth.info) && this.expectedLength == oth.expectedLength;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.digestAlgorithm));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.prk));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.info));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.expectedLength));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Aws.Cryptography.Primitives.Types_Compile.HkdfExpandInput.HkdfExpandInput";
      s += "(";
      s += Dafny.Helpers.ToString(this.digestAlgorithm);
      s += ", ";
      s += Dafny.Helpers.ToString(this.prk);
      s += ", ";
      s += Dafny.Helpers.ToString(this.info);
      s += ", ";
      s += Dafny.Helpers.ToString(this.expectedLength);
      s += ")";
      return s;
    }
    private static readonly _IHkdfExpandInput theDefault = create(Dafny.Aws.Cryptography.Primitives.Types.DigestAlgorithm.Default(), Dafny.Sequence<byte>.Empty, Dafny.Sequence<byte>.Empty, 0);
    public static _IHkdfExpandInput Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.Aws.Cryptography.Primitives.Types._IHkdfExpandInput> _TYPE = new Dafny.TypeDescriptor<Dafny.Aws.Cryptography.Primitives.Types._IHkdfExpandInput>(Dafny.Aws.Cryptography.Primitives.Types.HkdfExpandInput.Default());
    public static Dafny.TypeDescriptor<Dafny.Aws.Cryptography.Primitives.Types._IHkdfExpandInput> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IHkdfExpandInput create(Dafny.Aws.Cryptography.Primitives.Types._IDigestAlgorithm digestAlgorithm, Dafny.ISequence<byte> prk, Dafny.ISequence<byte> info, int expectedLength) {
      return new HkdfExpandInput(digestAlgorithm, prk, info, expectedLength);
    }
    public bool is_HkdfExpandInput { get { return true; } }
    public Dafny.Aws.Cryptography.Primitives.Types._IDigestAlgorithm dtor_digestAlgorithm {
      get {
        return this.digestAlgorithm;
      }
    }
    public Dafny.ISequence<byte> dtor_prk {
      get {
        return this.prk;
      }
    }
    public Dafny.ISequence<byte> dtor_info {
      get {
        return this.info;
      }
    }
    public int dtor_expectedLength {
      get {
        return this.expectedLength;
      }
    }
  }

  public interface _IHkdfExtractInput {
    bool is_HkdfExtractInput { get; }
    Dafny.Aws.Cryptography.Primitives.Types._IDigestAlgorithm dtor_digestAlgorithm { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_salt { get; }
    Dafny.ISequence<byte> dtor_ikm { get; }
    _IHkdfExtractInput DowncastClone();
  }
  public class HkdfExtractInput : _IHkdfExtractInput {
    public readonly Dafny.Aws.Cryptography.Primitives.Types._IDigestAlgorithm digestAlgorithm;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<byte>> salt;
    public readonly Dafny.ISequence<byte> ikm;
    public HkdfExtractInput(Dafny.Aws.Cryptography.Primitives.Types._IDigestAlgorithm digestAlgorithm, Wrappers_Compile._IOption<Dafny.ISequence<byte>> salt, Dafny.ISequence<byte> ikm) {
      this.digestAlgorithm = digestAlgorithm;
      this.salt = salt;
      this.ikm = ikm;
    }
    public _IHkdfExtractInput DowncastClone() {
      if (this is _IHkdfExtractInput dt) { return dt; }
      return new HkdfExtractInput(digestAlgorithm, salt, ikm);
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Aws.Cryptography.Primitives.Types.HkdfExtractInput;
      return oth != null && object.Equals(this.digestAlgorithm, oth.digestAlgorithm) && object.Equals(this.salt, oth.salt) && object.Equals(this.ikm, oth.ikm);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.digestAlgorithm));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.salt));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.ikm));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Aws.Cryptography.Primitives.Types_Compile.HkdfExtractInput.HkdfExtractInput";
      s += "(";
      s += Dafny.Helpers.ToString(this.digestAlgorithm);
      s += ", ";
      s += Dafny.Helpers.ToString(this.salt);
      s += ", ";
      s += Dafny.Helpers.ToString(this.ikm);
      s += ")";
      return s;
    }
    private static readonly _IHkdfExtractInput theDefault = create(Dafny.Aws.Cryptography.Primitives.Types.DigestAlgorithm.Default(), Wrappers_Compile.Option<Dafny.ISequence<byte>>.Default(), Dafny.Sequence<byte>.Empty);
    public static _IHkdfExtractInput Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.Aws.Cryptography.Primitives.Types._IHkdfExtractInput> _TYPE = new Dafny.TypeDescriptor<Dafny.Aws.Cryptography.Primitives.Types._IHkdfExtractInput>(Dafny.Aws.Cryptography.Primitives.Types.HkdfExtractInput.Default());
    public static Dafny.TypeDescriptor<Dafny.Aws.Cryptography.Primitives.Types._IHkdfExtractInput> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IHkdfExtractInput create(Dafny.Aws.Cryptography.Primitives.Types._IDigestAlgorithm digestAlgorithm, Wrappers_Compile._IOption<Dafny.ISequence<byte>> salt, Dafny.ISequence<byte> ikm) {
      return new HkdfExtractInput(digestAlgorithm, salt, ikm);
    }
    public bool is_HkdfExtractInput { get { return true; } }
    public Dafny.Aws.Cryptography.Primitives.Types._IDigestAlgorithm dtor_digestAlgorithm {
      get {
        return this.digestAlgorithm;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_salt {
      get {
        return this.salt;
      }
    }
    public Dafny.ISequence<byte> dtor_ikm {
      get {
        return this.ikm;
      }
    }
  }

  public interface _IHkdfInput {
    bool is_HkdfInput { get; }
    Dafny.Aws.Cryptography.Primitives.Types._IDigestAlgorithm dtor_digestAlgorithm { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_salt { get; }
    Dafny.ISequence<byte> dtor_ikm { get; }
    Dafny.ISequence<byte> dtor_info { get; }
    int dtor_expectedLength { get; }
    _IHkdfInput DowncastClone();
  }
  public class HkdfInput : _IHkdfInput {
    public readonly Dafny.Aws.Cryptography.Primitives.Types._IDigestAlgorithm digestAlgorithm;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<byte>> salt;
    public readonly Dafny.ISequence<byte> ikm;
    public readonly Dafny.ISequence<byte> info;
    public readonly int expectedLength;
    public HkdfInput(Dafny.Aws.Cryptography.Primitives.Types._IDigestAlgorithm digestAlgorithm, Wrappers_Compile._IOption<Dafny.ISequence<byte>> salt, Dafny.ISequence<byte> ikm, Dafny.ISequence<byte> info, int expectedLength) {
      this.digestAlgorithm = digestAlgorithm;
      this.salt = salt;
      this.ikm = ikm;
      this.info = info;
      this.expectedLength = expectedLength;
    }
    public _IHkdfInput DowncastClone() {
      if (this is _IHkdfInput dt) { return dt; }
      return new HkdfInput(digestAlgorithm, salt, ikm, info, expectedLength);
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Aws.Cryptography.Primitives.Types.HkdfInput;
      return oth != null && object.Equals(this.digestAlgorithm, oth.digestAlgorithm) && object.Equals(this.salt, oth.salt) && object.Equals(this.ikm, oth.ikm) && object.Equals(this.info, oth.info) && this.expectedLength == oth.expectedLength;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.digestAlgorithm));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.salt));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.ikm));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.info));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.expectedLength));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Aws.Cryptography.Primitives.Types_Compile.HkdfInput.HkdfInput";
      s += "(";
      s += Dafny.Helpers.ToString(this.digestAlgorithm);
      s += ", ";
      s += Dafny.Helpers.ToString(this.salt);
      s += ", ";
      s += Dafny.Helpers.ToString(this.ikm);
      s += ", ";
      s += Dafny.Helpers.ToString(this.info);
      s += ", ";
      s += Dafny.Helpers.ToString(this.expectedLength);
      s += ")";
      return s;
    }
    private static readonly _IHkdfInput theDefault = create(Dafny.Aws.Cryptography.Primitives.Types.DigestAlgorithm.Default(), Wrappers_Compile.Option<Dafny.ISequence<byte>>.Default(), Dafny.Sequence<byte>.Empty, Dafny.Sequence<byte>.Empty, 0);
    public static _IHkdfInput Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.Aws.Cryptography.Primitives.Types._IHkdfInput> _TYPE = new Dafny.TypeDescriptor<Dafny.Aws.Cryptography.Primitives.Types._IHkdfInput>(Dafny.Aws.Cryptography.Primitives.Types.HkdfInput.Default());
    public static Dafny.TypeDescriptor<Dafny.Aws.Cryptography.Primitives.Types._IHkdfInput> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IHkdfInput create(Dafny.Aws.Cryptography.Primitives.Types._IDigestAlgorithm digestAlgorithm, Wrappers_Compile._IOption<Dafny.ISequence<byte>> salt, Dafny.ISequence<byte> ikm, Dafny.ISequence<byte> info, int expectedLength) {
      return new HkdfInput(digestAlgorithm, salt, ikm, info, expectedLength);
    }
    public bool is_HkdfInput { get { return true; } }
    public Dafny.Aws.Cryptography.Primitives.Types._IDigestAlgorithm dtor_digestAlgorithm {
      get {
        return this.digestAlgorithm;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_salt {
      get {
        return this.salt;
      }
    }
    public Dafny.ISequence<byte> dtor_ikm {
      get {
        return this.ikm;
      }
    }
    public Dafny.ISequence<byte> dtor_info {
      get {
        return this.info;
      }
    }
    public int dtor_expectedLength {
      get {
        return this.expectedLength;
      }
    }
  }

  public interface _IHMacInput {
    bool is_HMacInput { get; }
    Dafny.Aws.Cryptography.Primitives.Types._IDigestAlgorithm dtor_digestAlgorithm { get; }
    Dafny.ISequence<byte> dtor_key { get; }
    Dafny.ISequence<byte> dtor_message { get; }
    _IHMacInput DowncastClone();
  }
  public class HMacInput : _IHMacInput {
    public readonly Dafny.Aws.Cryptography.Primitives.Types._IDigestAlgorithm digestAlgorithm;
    public readonly Dafny.ISequence<byte> key;
    public readonly Dafny.ISequence<byte> message;
    public HMacInput(Dafny.Aws.Cryptography.Primitives.Types._IDigestAlgorithm digestAlgorithm, Dafny.ISequence<byte> key, Dafny.ISequence<byte> message) {
      this.digestAlgorithm = digestAlgorithm;
      this.key = key;
      this.message = message;
    }
    public _IHMacInput DowncastClone() {
      if (this is _IHMacInput dt) { return dt; }
      return new HMacInput(digestAlgorithm, key, message);
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Aws.Cryptography.Primitives.Types.HMacInput;
      return oth != null && object.Equals(this.digestAlgorithm, oth.digestAlgorithm) && object.Equals(this.key, oth.key) && object.Equals(this.message, oth.message);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.digestAlgorithm));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.key));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.message));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Aws.Cryptography.Primitives.Types_Compile.HMacInput.HMacInput";
      s += "(";
      s += Dafny.Helpers.ToString(this.digestAlgorithm);
      s += ", ";
      s += Dafny.Helpers.ToString(this.key);
      s += ", ";
      s += Dafny.Helpers.ToString(this.message);
      s += ")";
      return s;
    }
    private static readonly _IHMacInput theDefault = create(Dafny.Aws.Cryptography.Primitives.Types.DigestAlgorithm.Default(), Dafny.Sequence<byte>.Empty, Dafny.Sequence<byte>.Empty);
    public static _IHMacInput Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.Aws.Cryptography.Primitives.Types._IHMacInput> _TYPE = new Dafny.TypeDescriptor<Dafny.Aws.Cryptography.Primitives.Types._IHMacInput>(Dafny.Aws.Cryptography.Primitives.Types.HMacInput.Default());
    public static Dafny.TypeDescriptor<Dafny.Aws.Cryptography.Primitives.Types._IHMacInput> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IHMacInput create(Dafny.Aws.Cryptography.Primitives.Types._IDigestAlgorithm digestAlgorithm, Dafny.ISequence<byte> key, Dafny.ISequence<byte> message) {
      return new HMacInput(digestAlgorithm, key, message);
    }
    public bool is_HMacInput { get { return true; } }
    public Dafny.Aws.Cryptography.Primitives.Types._IDigestAlgorithm dtor_digestAlgorithm {
      get {
        return this.digestAlgorithm;
      }
    }
    public Dafny.ISequence<byte> dtor_key {
      get {
        return this.key;
      }
    }
    public Dafny.ISequence<byte> dtor_message {
      get {
        return this.message;
      }
    }
  }

  public partial class PositiveInteger {
    private static readonly Dafny.TypeDescriptor<int> _TYPE = new Dafny.TypeDescriptor<int>(0);
    public static Dafny.TypeDescriptor<int> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public interface _IError {
    bool is_AwsCryptographicPrimitivesError { get; }
    bool is_Opaque { get; }
    Dafny.ISequence<char> dtor_message { get; }
    object dtor_obj { get; }
    _IError DowncastClone();
  }
  public abstract class Error : _IError {
    public Error() { }
    private static readonly _IError theDefault = create_AwsCryptographicPrimitivesError(Dafny.Sequence<char>.Empty);
    public static _IError Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.Aws.Cryptography.Primitives.Types._IError> _TYPE = new Dafny.TypeDescriptor<Dafny.Aws.Cryptography.Primitives.Types._IError>(Dafny.Aws.Cryptography.Primitives.Types.Error.Default());
    public static Dafny.TypeDescriptor<Dafny.Aws.Cryptography.Primitives.Types._IError> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IError create_AwsCryptographicPrimitivesError(Dafny.ISequence<char> message) {
      return new Error_AwsCryptographicPrimitivesError(message);
    }
    public static _IError create_Opaque(object obj) {
      return new Error_Opaque(obj);
    }
    public bool is_AwsCryptographicPrimitivesError { get { return this is Error_AwsCryptographicPrimitivesError; } }
    public bool is_Opaque { get { return this is Error_Opaque; } }
    public Dafny.ISequence<char> dtor_message {
      get {
        var d = this;
        return ((Error_AwsCryptographicPrimitivesError)d).message;
      }
    }
    public object dtor_obj {
      get {
        var d = this;
        return ((Error_Opaque)d).obj;
      }
    }
    public abstract _IError DowncastClone();
  }
  public class Error_AwsCryptographicPrimitivesError : Error {
    public readonly Dafny.ISequence<char> message;
    public Error_AwsCryptographicPrimitivesError(Dafny.ISequence<char> message) {
      this.message = message;
    }
    public override _IError DowncastClone() {
      if (this is _IError dt) { return dt; }
      return new Error_AwsCryptographicPrimitivesError(message);
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Aws.Cryptography.Primitives.Types.Error_AwsCryptographicPrimitivesError;
      return oth != null && object.Equals(this.message, oth.message);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.message));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Aws.Cryptography.Primitives.Types_Compile.Error.AwsCryptographicPrimitivesError";
      s += "(";
      s += Dafny.Helpers.ToString(this.message);
      s += ")";
      return s;
    }
  }
  public class Error_Opaque : Error {
    public readonly object obj;
    public Error_Opaque(object obj) {
      this.obj = obj;
    }
    public override _IError DowncastClone() {
      if (this is _IError dt) { return dt; }
      return new Error_Opaque(obj);
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Aws.Cryptography.Primitives.Types.Error_Opaque;
      return oth != null && this.obj == oth.obj;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.obj));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Aws.Cryptography.Primitives.Types_Compile.Error.Opaque";
      s += "(";
      s += Dafny.Helpers.ToString(this.obj);
      s += ")";
      return s;
    }
  }

  public partial class OpaqueError {
    private static readonly Dafny.TypeDescriptor<Dafny.Aws.Cryptography.Primitives.Types._IError> _TYPE = new Dafny.TypeDescriptor<Dafny.Aws.Cryptography.Primitives.Types._IError>(Dafny.Aws.Cryptography.Primitives.Types.Error.Default());
    public static Dafny.TypeDescriptor<Dafny.Aws.Cryptography.Primitives.Types._IError> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class __default {
    public static bool IsValid__PositiveInteger(int x) {
      return (0) <= (x);
    }
  }
} // end of namespace Dafny.Aws.Cryptography.Primitives.Types
namespace ExternDigest {

} // end of namespace ExternDigest
namespace Digest_Compile {

  public partial class __default {
    public static BigInteger Length(Dafny.Aws.Cryptography.Primitives.Types._IDigestAlgorithm digestAlgorithm) {
      Dafny.Aws.Cryptography.Primitives.Types._IDigestAlgorithm _source5 = digestAlgorithm;
      if (_source5.is_SHA__512) {
        return new BigInteger(64);
      } else if (_source5.is_SHA__384) {
        return new BigInteger(48);
      } else {
        return new BigInteger(32);
      }
    }
    public static Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.Aws.Cryptography.Primitives.Types._IError> Digest(Dafny.Aws.Cryptography.Primitives.Types._IDigestInput input)
    {
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.Aws.Cryptography.Primitives.Types._IError> res = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.Aws.Cryptography.Primitives.Types._IError>.Default(Dafny.Sequence<byte>.Empty);
      Dafny.Aws.Cryptography.Primitives.Types._IDigestInput _let_tmp_rhs0 = input;
      Dafny.Aws.Cryptography.Primitives.Types._IDigestAlgorithm _76_digestAlgorithm = _let_tmp_rhs0.dtor_digestAlgorithm;
      Dafny.ISequence<byte> _77_message = _let_tmp_rhs0.dtor_message;
      Dafny.ISequence<byte> _78_value;
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.Aws.Cryptography.Primitives.Types._IError> _79_valueOrError0 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.Aws.Cryptography.Primitives.Types._IError>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.Aws.Cryptography.Primitives.Types._IError> _out0;
      _out0 = ExternDigest.__default.Digest(_76_digestAlgorithm, _77_message);
      _79_valueOrError0 = _out0;
      if ((_79_valueOrError0).IsFailure()) {
        res = (_79_valueOrError0).PropagateFailure<Dafny.ISequence<byte>>();
        return res;
      }
      _78_value = (_79_valueOrError0).Extract();
      Wrappers_Compile._IOutcome<Dafny.Aws.Cryptography.Primitives.Types._IError> _80_valueOrError1 = Wrappers_Compile.Outcome<Dafny.Aws.Cryptography.Primitives.Types._IError>.Default();
      _80_valueOrError1 = Wrappers_Compile.__default.Need<Dafny.Aws.Cryptography.Primitives.Types._IError>((new BigInteger((_78_value).Count)) == (Digest_Compile.__default.Length(_76_digestAlgorithm)), Dafny.Aws.Cryptography.Primitives.Types.Error.create_AwsCryptographicPrimitivesError(Dafny.Sequence<char>.FromString("Incorrect length digest from ExternDigest.")));
      if ((_80_valueOrError1).IsFailure()) {
        res = (_80_valueOrError1).PropagateFailure<Dafny.ISequence<byte>>();
        return res;
      }
      res = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.Aws.Cryptography.Primitives.Types._IError>.create_Success(_78_value);
      return res;
      return res;
    }
  }
} // end of namespace Digest_Compile
namespace HMAC {


} // end of namespace HMAC
namespace HKDF_Compile {

  public partial class __default {
    public static Dafny.ISequence<byte> Extract(HMAC.HMac hmac, Dafny.ISequence<byte> salt, Dafny.ISequence<byte> ikm)
    {
      Dafny.ISequence<byte> prk = Dafny.Sequence<byte>.Empty;
      (hmac).Init(salt);
      (hmac).BlockUpdate(ikm);
      Dafny.ISequence<byte> _out1;
      _out1 = (hmac).GetResult();
      prk = _out1;
      prk = prk;
      return prk;
      return prk;
    }
    public static Dafny.ISequence<byte> Expand(HMAC.HMac hmac, Dafny.ISequence<byte> prk, Dafny.ISequence<byte> info, BigInteger expectedLength, Dafny.Aws.Cryptography.Primitives.Types._IDigestAlgorithm digest)
    {
      Dafny.ISequence<byte> okm = Dafny.Sequence<byte>.Empty;
      BigInteger _81_hashLength;
      _81_hashLength = Digest_Compile.__default.Length(digest);
      BigInteger _82_n;
      _82_n = Dafny.Helpers.EuclideanDivision(((_81_hashLength) + (expectedLength)) - (BigInteger.One), _81_hashLength);
      (hmac).Init(prk);
      Dafny.ISequence<byte> _83_t__prev;
      _83_t__prev = Dafny.Sequence<byte>.FromElements();
      Dafny.ISequence<byte> _84_t__n;
      _84_t__n = _83_t__prev;
      BigInteger _85_i;
      _85_i = BigInteger.One;
      while ((_85_i) <= (_82_n)) {
        (hmac).BlockUpdate(_83_t__prev);
        (hmac).BlockUpdate(info);
        (hmac).BlockUpdate(Dafny.Sequence<byte>.FromElements((byte)(_85_i)));
        Dafny.ISequence<byte> _out2;
        _out2 = (hmac).GetResult();
        _83_t__prev = _out2;
        _84_t__n = Dafny.Sequence<byte>.Concat(_84_t__n, _83_t__prev);
        _85_i = (_85_i) + (BigInteger.One);
      }
      okm = _84_t__n;
      if ((expectedLength) < (new BigInteger((okm).Count))) {
        okm = (okm).Take(expectedLength);
      }
      return okm;
    }
    public static Dafny.ISequence<byte> Hkdf(Dafny.Aws.Cryptography.Primitives.Types._IDigestAlgorithm digest, Wrappers_Compile._IOption<Dafny.ISequence<byte>> salt, Dafny.ISequence<byte> ikm, Dafny.ISequence<byte> info, BigInteger L)
    {
      Dafny.ISequence<byte> okm = Dafny.Sequence<byte>.Empty;
      if ((L).Sign == 0) {
        okm = Dafny.Sequence<byte>.FromElements();
        return okm;
      }
      HMAC.HMac _86_hmac;
      HMAC.HMac _nw1 = new HMAC.HMac(digest);
      _86_hmac = _nw1;
      BigInteger _87_hashLength;
      _87_hashLength = Digest_Compile.__default.Length(digest);
      Dafny.ISequence<byte> _88_nonEmptySalt = Dafny.Sequence<byte>.Empty;
      Wrappers_Compile._IOption<Dafny.ISequence<byte>> _source6 = salt;
      if (_source6.is_None) {
        _88_nonEmptySalt = StandardLibrary_Compile.__default.Fill<byte>(0, _87_hashLength);
      } else {
        Dafny.ISequence<byte> _89___mcc_h0 = _source6.dtor_value;
        Dafny.ISequence<byte> _90_s = _89___mcc_h0;
        _88_nonEmptySalt = _90_s;
      }
      Dafny.ISequence<byte> _91_prk;
      Dafny.ISequence<byte> _out3;
      _out3 = HKDF_Compile.__default.Extract(_86_hmac, _88_nonEmptySalt, ikm);
      _91_prk = _out3;
      Dafny.ISequence<byte> _out4;
      _out4 = HKDF_Compile.__default.Expand(_86_hmac, _91_prk, info, L, digest);
      okm = _out4;
      return okm;
    }
  }
} // end of namespace HKDF_Compile
namespace AESEncryption {

  public partial class __default {
    public static Dafny.Aws.Cryptography.Primitives.Types._IAESEncryptOutput EncryptionOutputFromByteSeq(Dafny.ISequence<byte> s, Dafny.Aws.Cryptography.Primitives.Types._IAES__GCM encAlg)
    {
      Dafny.ISequence<byte> _92_cipherText = (s).Take((new BigInteger((s).Count)) - (new BigInteger((encAlg).dtor_tagLength)));
      Dafny.ISequence<byte> _93_authTag = (s).Drop((new BigInteger((s).Count)) - (new BigInteger((encAlg).dtor_tagLength)));
      return Dafny.Aws.Cryptography.Primitives.Types.AESEncryptOutput.create(_92_cipherText, _93_authTag);
    }
    public static Wrappers_Compile._IResult<Dafny.Aws.Cryptography.Primitives.Types._IAESEncryptOutput, Dafny.Aws.Cryptography.Primitives.Types._IError> AESEncrypt(Dafny.Aws.Cryptography.Primitives.Types._IAESEncryptInput input)
    {
      Wrappers_Compile._IResult<Dafny.Aws.Cryptography.Primitives.Types._IAESEncryptOutput, Dafny.Aws.Cryptography.Primitives.Types._IError> res = Wrappers_Compile.Result<Dafny.Aws.Cryptography.Primitives.Types._IAESEncryptOutput, Dafny.Aws.Cryptography.Primitives.Types._IError>.Default(Dafny.Aws.Cryptography.Primitives.Types.AESEncryptOutput.Default());
      Dafny.Aws.Cryptography.Primitives.Types._IAESEncryptInput _let_tmp_rhs1 = input;
      Dafny.Aws.Cryptography.Primitives.Types._IAES__GCM _94_encAlg = _let_tmp_rhs1.dtor_encAlg;
      Dafny.ISequence<byte> _95_iv = _let_tmp_rhs1.dtor_iv;
      Dafny.ISequence<byte> _96_key = _let_tmp_rhs1.dtor_key;
      Dafny.ISequence<byte> _97_msg = _let_tmp_rhs1.dtor_msg;
      Dafny.ISequence<byte> _98_aad = _let_tmp_rhs1.dtor_aad;
      Dafny.Aws.Cryptography.Primitives.Types._IAESEncryptOutput _99_value;
      Wrappers_Compile._IResult<Dafny.Aws.Cryptography.Primitives.Types._IAESEncryptOutput, Dafny.Aws.Cryptography.Primitives.Types._IError> _100_valueOrError0 = Wrappers_Compile.Result<Dafny.Aws.Cryptography.Primitives.Types._IAESEncryptOutput, Dafny.Aws.Cryptography.Primitives.Types._IError>.Default(Dafny.Aws.Cryptography.Primitives.Types.AESEncryptOutput.Default());
      Wrappers_Compile._IResult<Dafny.Aws.Cryptography.Primitives.Types._IAESEncryptOutput, Dafny.Aws.Cryptography.Primitives.Types._IError> _out5;
      _out5 = AESEncryption.AES_GCM.AESEncryptExtern(_94_encAlg, _95_iv, _96_key, _97_msg, _98_aad);
      _100_valueOrError0 = _out5;
      if ((_100_valueOrError0).IsFailure()) {
        res = (_100_valueOrError0).PropagateFailure<Dafny.Aws.Cryptography.Primitives.Types._IAESEncryptOutput>();
        return res;
      }
      _99_value = (_100_valueOrError0).Extract();
      Wrappers_Compile._IOutcome<Dafny.Aws.Cryptography.Primitives.Types._IError> _101_valueOrError1 = Wrappers_Compile.Outcome<Dafny.Aws.Cryptography.Primitives.Types._IError>.Default();
      _101_valueOrError1 = Wrappers_Compile.__default.Need<Dafny.Aws.Cryptography.Primitives.Types._IError>((new BigInteger(((_99_value).dtor_cipherText).Count)) == (new BigInteger((_97_msg).Count)), Dafny.Aws.Cryptography.Primitives.Types.Error.create_AwsCryptographicPrimitivesError(Dafny.Sequence<char>.FromString("AESEncrypt did not return cipherText of expected length")));
      if ((_101_valueOrError1).IsFailure()) {
        res = (_101_valueOrError1).PropagateFailure<Dafny.Aws.Cryptography.Primitives.Types._IAESEncryptOutput>();
        return res;
      }
      Wrappers_Compile._IOutcome<Dafny.Aws.Cryptography.Primitives.Types._IError> _102_valueOrError2 = Wrappers_Compile.Outcome<Dafny.Aws.Cryptography.Primitives.Types._IError>.Default();
      _102_valueOrError2 = Wrappers_Compile.__default.Need<Dafny.Aws.Cryptography.Primitives.Types._IError>((new BigInteger(((_99_value).dtor_authTag).Count)) == (new BigInteger((_94_encAlg).dtor_tagLength)), Dafny.Aws.Cryptography.Primitives.Types.Error.create_AwsCryptographicPrimitivesError(Dafny.Sequence<char>.FromString("AESEncryption did not return valid tag")));
      if ((_102_valueOrError2).IsFailure()) {
        res = (_102_valueOrError2).PropagateFailure<Dafny.Aws.Cryptography.Primitives.Types._IAESEncryptOutput>();
        return res;
      }
      res = Wrappers_Compile.Result<Dafny.Aws.Cryptography.Primitives.Types._IAESEncryptOutput, Dafny.Aws.Cryptography.Primitives.Types._IError>.create_Success(_99_value);
      return res;
      return res;
    }
    public static Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.Aws.Cryptography.Primitives.Types._IError> AESDecrypt(Dafny.Aws.Cryptography.Primitives.Types._IAESDecryptInput input)
    {
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.Aws.Cryptography.Primitives.Types._IError> res = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.Aws.Cryptography.Primitives.Types._IError>.Default(Dafny.Sequence<byte>.Empty);
      Dafny.Aws.Cryptography.Primitives.Types._IAESDecryptInput _let_tmp_rhs2 = input;
      Dafny.Aws.Cryptography.Primitives.Types._IAES__GCM _103_encAlg = _let_tmp_rhs2.dtor_encAlg;
      Dafny.ISequence<byte> _104_key = _let_tmp_rhs2.dtor_key;
      Dafny.ISequence<byte> _105_cipherTxt = _let_tmp_rhs2.dtor_cipherTxt;
      Dafny.ISequence<byte> _106_authTag = _let_tmp_rhs2.dtor_authTag;
      Dafny.ISequence<byte> _107_iv = _let_tmp_rhs2.dtor_iv;
      Dafny.ISequence<byte> _108_aad = _let_tmp_rhs2.dtor_aad;
      Dafny.ISequence<byte> _109_value;
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.Aws.Cryptography.Primitives.Types._IError> _110_valueOrError0 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.Aws.Cryptography.Primitives.Types._IError>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.Aws.Cryptography.Primitives.Types._IError> _out6;
      _out6 = AESEncryption.AES_GCM.AESDecryptExtern(_103_encAlg, _104_key, _105_cipherTxt, _106_authTag, _107_iv, _108_aad);
      _110_valueOrError0 = _out6;
      if ((_110_valueOrError0).IsFailure()) {
        res = (_110_valueOrError0).PropagateFailure<Dafny.ISequence<byte>>();
        return res;
      }
      _109_value = (_110_valueOrError0).Extract();
      Wrappers_Compile._IOutcome<Dafny.Aws.Cryptography.Primitives.Types._IError> _111_valueOrError1 = Wrappers_Compile.Outcome<Dafny.Aws.Cryptography.Primitives.Types._IError>.Default();
      _111_valueOrError1 = Wrappers_Compile.__default.Need<Dafny.Aws.Cryptography.Primitives.Types._IError>((new BigInteger((_105_cipherTxt).Count)) == (new BigInteger((_109_value).Count)), Dafny.Aws.Cryptography.Primitives.Types.Error.create_AwsCryptographicPrimitivesError(Dafny.Sequence<char>.FromString("AESDecrypt did not return plaintext of expected length")));
      if ((_111_valueOrError1).IsFailure()) {
        res = (_111_valueOrError1).PropagateFailure<Dafny.ISequence<byte>>();
        return res;
      }
      res = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.Aws.Cryptography.Primitives.Types._IError>.create_Success(_109_value);
      return res;
      return res;
    }
  }
} // end of namespace AESEncryption
namespace RSAEncryption {

  public interface _IPaddingMode {
    bool is_PKCS1 { get; }
    bool is_OAEP__SHA1 { get; }
    bool is_OAEP__SHA256 { get; }
    bool is_OAEP__SHA384 { get; }
    bool is_OAEP__SHA512 { get; }
    _IPaddingMode DowncastClone();
  }
  public abstract class PaddingMode : _IPaddingMode {
    public PaddingMode() { }
    private static readonly _IPaddingMode theDefault = create_PKCS1();
    public static _IPaddingMode Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<RSAEncryption._IPaddingMode> _TYPE = new Dafny.TypeDescriptor<RSAEncryption._IPaddingMode>(RSAEncryption.PaddingMode.Default());
    public static Dafny.TypeDescriptor<RSAEncryption._IPaddingMode> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IPaddingMode create_PKCS1() {
      return new PaddingMode_PKCS1();
    }
    public static _IPaddingMode create_OAEP__SHA1() {
      return new PaddingMode_OAEP__SHA1();
    }
    public static _IPaddingMode create_OAEP__SHA256() {
      return new PaddingMode_OAEP__SHA256();
    }
    public static _IPaddingMode create_OAEP__SHA384() {
      return new PaddingMode_OAEP__SHA384();
    }
    public static _IPaddingMode create_OAEP__SHA512() {
      return new PaddingMode_OAEP__SHA512();
    }
    public bool is_PKCS1 { get { return this is PaddingMode_PKCS1; } }
    public bool is_OAEP__SHA1 { get { return this is PaddingMode_OAEP__SHA1; } }
    public bool is_OAEP__SHA256 { get { return this is PaddingMode_OAEP__SHA256; } }
    public bool is_OAEP__SHA384 { get { return this is PaddingMode_OAEP__SHA384; } }
    public bool is_OAEP__SHA512 { get { return this is PaddingMode_OAEP__SHA512; } }
    public static System.Collections.Generic.IEnumerable<_IPaddingMode> AllSingletonConstructors {
      get {
        yield return PaddingMode.create_PKCS1();
        yield return PaddingMode.create_OAEP__SHA1();
        yield return PaddingMode.create_OAEP__SHA256();
        yield return PaddingMode.create_OAEP__SHA384();
        yield return PaddingMode.create_OAEP__SHA512();
      }
    }
    public abstract _IPaddingMode DowncastClone();
  }
  public class PaddingMode_PKCS1 : PaddingMode {
    public PaddingMode_PKCS1() {
    }
    public override _IPaddingMode DowncastClone() {
      if (this is _IPaddingMode dt) { return dt; }
      return new PaddingMode_PKCS1();
    }
    public override bool Equals(object other) {
      var oth = other as RSAEncryption.PaddingMode_PKCS1;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "RSAEncryption_Compile.PaddingMode.PKCS1";
      return s;
    }
  }
  public class PaddingMode_OAEP__SHA1 : PaddingMode {
    public PaddingMode_OAEP__SHA1() {
    }
    public override _IPaddingMode DowncastClone() {
      if (this is _IPaddingMode dt) { return dt; }
      return new PaddingMode_OAEP__SHA1();
    }
    public override bool Equals(object other) {
      var oth = other as RSAEncryption.PaddingMode_OAEP__SHA1;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "RSAEncryption_Compile.PaddingMode.OAEP_SHA1";
      return s;
    }
  }
  public class PaddingMode_OAEP__SHA256 : PaddingMode {
    public PaddingMode_OAEP__SHA256() {
    }
    public override _IPaddingMode DowncastClone() {
      if (this is _IPaddingMode dt) { return dt; }
      return new PaddingMode_OAEP__SHA256();
    }
    public override bool Equals(object other) {
      var oth = other as RSAEncryption.PaddingMode_OAEP__SHA256;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      return (int) hash;
    }
    public override string ToString() {
      string s = "RSAEncryption_Compile.PaddingMode.OAEP_SHA256";
      return s;
    }
  }
  public class PaddingMode_OAEP__SHA384 : PaddingMode {
    public PaddingMode_OAEP__SHA384() {
    }
    public override _IPaddingMode DowncastClone() {
      if (this is _IPaddingMode dt) { return dt; }
      return new PaddingMode_OAEP__SHA384();
    }
    public override bool Equals(object other) {
      var oth = other as RSAEncryption.PaddingMode_OAEP__SHA384;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      return (int) hash;
    }
    public override string ToString() {
      string s = "RSAEncryption_Compile.PaddingMode.OAEP_SHA384";
      return s;
    }
  }
  public class PaddingMode_OAEP__SHA512 : PaddingMode {
    public PaddingMode_OAEP__SHA512() {
    }
    public override _IPaddingMode DowncastClone() {
      if (this is _IPaddingMode dt) { return dt; }
      return new PaddingMode_OAEP__SHA512();
    }
    public override bool Equals(object other) {
      var oth = other as RSAEncryption.PaddingMode_OAEP__SHA512;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 4;
      return (int) hash;
    }
    public override string ToString() {
      string s = "RSAEncryption_Compile.PaddingMode.OAEP_SHA512";
      return s;
    }
  }

  public partial class StrengthBits {
    public static System.Collections.Generic.IEnumerable<int> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (int)j; }
    }
    public static readonly int Witness = (int)(new BigInteger(81));
    private static readonly Dafny.TypeDescriptor<int> _TYPE = new Dafny.TypeDescriptor<int>(RSAEncryption.StrengthBits.Witness);
    public static Dafny.TypeDescriptor<int> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public interface Key {
    int strength { get; }
    Dafny.ISequence<byte> pem { get; }
  }
  public class _Companion_Key {
  }

  public partial class PrivateKey : RSAEncryption.Key {
    public PrivateKey() {
      this._strength = RSAEncryption.StrengthBits.Witness;
      this._pem = Dafny.Sequence<byte>.Empty;
    }
    public  int _strength {get; set;}
    public int strength { get {
      return this._strength;
    } }
    public  Dafny.ISequence<byte> _pem {get; set;}
    public Dafny.ISequence<byte> pem { get {
      return this._pem;
    } }
    public void __ctor(Dafny.ISequence<byte> pem, int strength)
    {
      (this)._pem = pem;
      (this)._strength = strength;
    }
  }

  public partial class PublicKey : RSAEncryption.Key {
    public PublicKey() {
      this._strength = RSAEncryption.StrengthBits.Witness;
      this._pem = Dafny.Sequence<byte>.Empty;
    }
    public  int _strength {get; set;}
    public int strength { get {
      return this._strength;
    } }
    public  Dafny.ISequence<byte> _pem {get; set;}
    public Dafny.ISequence<byte> pem { get {
      return this._pem;
    } }
    public void __ctor(Dafny.ISequence<byte> pem, int strength)
    {
      (this)._pem = pem;
      (this)._strength = strength;
    }
  }

  public partial class __default {
    public static void GenerateKeyPair(int strength, out RSAEncryption.PublicKey publicKey, out RSAEncryption.PrivateKey privateKey)
    {
      publicKey = default(RSAEncryption.PublicKey);
      privateKey = default(RSAEncryption.PrivateKey);
      Dafny.ISequence<byte> _112_pemPublic;
      Dafny.ISequence<byte> _113_pemPrivate;
      Dafny.ISequence<byte> _out7;
      Dafny.ISequence<byte> _out8;
      RSAEncryption.RSA.GenerateKeyPairExtern(strength, out _out7, out _out8);
      _112_pemPublic = _out7;
      _113_pemPrivate = _out8;
      RSAEncryption.PrivateKey _nw2 = new RSAEncryption.PrivateKey();
      _nw2.__ctor(_113_pemPrivate, strength);
      privateKey = _nw2;
      RSAEncryption.PublicKey _nw3 = new RSAEncryption.PublicKey();
      _nw3.__ctor(_112_pemPublic, strength);
      publicKey = _nw3;
    }
  }
} // end of namespace RSAEncryption
namespace ExternRandom {

} // end of namespace ExternRandom
namespace Random_Compile {

  public partial class __default {
    public static Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.Aws.Cryptography.Primitives.Types._IError> GenerateBytes(int i)
    {
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.Aws.Cryptography.Primitives.Types._IError> res = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.Aws.Cryptography.Primitives.Types._IError>.Default(Dafny.Sequence<byte>.Empty);
      Dafny.ISequence<byte> _114_value;
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.Aws.Cryptography.Primitives.Types._IError> _115_valueOrError0 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.Aws.Cryptography.Primitives.Types._IError>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.Aws.Cryptography.Primitives.Types._IError> _out9;
      _out9 = ExternRandom.__default.GenerateBytes(i);
      _115_valueOrError0 = _out9;
      if ((_115_valueOrError0).IsFailure()) {
        res = (_115_valueOrError0).PropagateFailure<Dafny.ISequence<byte>>();
        return res;
      }
      _114_value = (_115_valueOrError0).Extract();
      Wrappers_Compile._IOutcome<Dafny.Aws.Cryptography.Primitives.Types._IError> _116_valueOrError1 = Wrappers_Compile.Outcome<Dafny.Aws.Cryptography.Primitives.Types._IError>.Default();
      _116_valueOrError1 = Wrappers_Compile.__default.Need<Dafny.Aws.Cryptography.Primitives.Types._IError>((new BigInteger((_114_value).Count)) == (new BigInteger(i)), Dafny.Aws.Cryptography.Primitives.Types.Error.create_AwsCryptographicPrimitivesError(Dafny.Sequence<char>.FromString("Incorrect length from ExternRandom.")));
      if ((_116_valueOrError1).IsFailure()) {
        res = (_116_valueOrError1).PropagateFailure<Dafny.ISequence<byte>>();
        return res;
      }
      res = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.Aws.Cryptography.Primitives.Types._IError>.create_Success(_114_value);
      return res;
      return res;
    }
  }
} // end of namespace Random_Compile
namespace Signature {

  public interface _ISignatureKeyPair {
    bool is_SignatureKeyPair { get; }
    Dafny.ISequence<byte> dtor_verificationKey { get; }
    Dafny.ISequence<byte> dtor_signingKey { get; }
    _ISignatureKeyPair DowncastClone();
  }
  public class SignatureKeyPair : _ISignatureKeyPair {
    public readonly Dafny.ISequence<byte> verificationKey;
    public readonly Dafny.ISequence<byte> signingKey;
    public SignatureKeyPair(Dafny.ISequence<byte> verificationKey, Dafny.ISequence<byte> signingKey) {
      this.verificationKey = verificationKey;
      this.signingKey = signingKey;
    }
    public _ISignatureKeyPair DowncastClone() {
      if (this is _ISignatureKeyPair dt) { return dt; }
      return new SignatureKeyPair(verificationKey, signingKey);
    }
    public override bool Equals(object other) {
      var oth = other as Signature.SignatureKeyPair;
      return oth != null && object.Equals(this.verificationKey, oth.verificationKey) && object.Equals(this.signingKey, oth.signingKey);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.verificationKey));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.signingKey));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Signature_Compile.SignatureKeyPair.SignatureKeyPair";
      s += "(";
      s += Dafny.Helpers.ToString(this.verificationKey);
      s += ", ";
      s += Dafny.Helpers.ToString(this.signingKey);
      s += ")";
      return s;
    }
    private static readonly _ISignatureKeyPair theDefault = create(Dafny.Sequence<byte>.Empty, Dafny.Sequence<byte>.Empty);
    public static _ISignatureKeyPair Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Signature._ISignatureKeyPair> _TYPE = new Dafny.TypeDescriptor<Signature._ISignatureKeyPair>(Signature.SignatureKeyPair.Default());
    public static Dafny.TypeDescriptor<Signature._ISignatureKeyPair> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ISignatureKeyPair create(Dafny.ISequence<byte> verificationKey, Dafny.ISequence<byte> signingKey) {
      return new SignatureKeyPair(verificationKey, signingKey);
    }
    public bool is_SignatureKeyPair { get { return true; } }
    public Dafny.ISequence<byte> dtor_verificationKey {
      get {
        return this.verificationKey;
      }
    }
    public Dafny.ISequence<byte> dtor_signingKey {
      get {
        return this.signingKey;
      }
    }
  }

  public interface _IECDSAParams {
    bool is_ECDSA__P384 { get; }
    bool is_ECDSA__P256 { get; }
    _IECDSAParams DowncastClone();
    ushort SignatureLength();
    BigInteger FieldSize();
  }
  public abstract class ECDSAParams : _IECDSAParams {
    public ECDSAParams() { }
    private static readonly _IECDSAParams theDefault = create_ECDSA__P384();
    public static _IECDSAParams Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Signature._IECDSAParams> _TYPE = new Dafny.TypeDescriptor<Signature._IECDSAParams>(Signature.ECDSAParams.Default());
    public static Dafny.TypeDescriptor<Signature._IECDSAParams> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IECDSAParams create_ECDSA__P384() {
      return new ECDSAParams_ECDSA__P384();
    }
    public static _IECDSAParams create_ECDSA__P256() {
      return new ECDSAParams_ECDSA__P256();
    }
    public bool is_ECDSA__P384 { get { return this is ECDSAParams_ECDSA__P384; } }
    public bool is_ECDSA__P256 { get { return this is ECDSAParams_ECDSA__P256; } }
    public static System.Collections.Generic.IEnumerable<_IECDSAParams> AllSingletonConstructors {
      get {
        yield return ECDSAParams.create_ECDSA__P384();
        yield return ECDSAParams.create_ECDSA__P256();
      }
    }
    public abstract _IECDSAParams DowncastClone();
    public ushort SignatureLength() {
      Signature._IECDSAParams _source7 = this;
      if (_source7.is_ECDSA__P384) {
        return 103;
      } else {
        return 71;
      }
    }
    public BigInteger FieldSize() {
      Signature._IECDSAParams _source8 = this;
      if (_source8.is_ECDSA__P384) {
        return new BigInteger(49);
      } else {
        return new BigInteger(33);
      }
    }
  }
  public class ECDSAParams_ECDSA__P384 : ECDSAParams {
    public ECDSAParams_ECDSA__P384() {
    }
    public override _IECDSAParams DowncastClone() {
      if (this is _IECDSAParams dt) { return dt; }
      return new ECDSAParams_ECDSA__P384();
    }
    public override bool Equals(object other) {
      var oth = other as Signature.ECDSAParams_ECDSA__P384;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Signature_Compile.ECDSAParams.ECDSA_P384";
      return s;
    }
  }
  public class ECDSAParams_ECDSA__P256 : ECDSAParams {
    public ECDSAParams_ECDSA__P256() {
    }
    public override _IECDSAParams DowncastClone() {
      if (this is _IECDSAParams dt) { return dt; }
      return new ECDSAParams_ECDSA__P256();
    }
    public override bool Equals(object other) {
      var oth = other as Signature.ECDSAParams_ECDSA__P256;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Signature_Compile.ECDSAParams.ECDSA_P256";
      return s;
    }
  }

  public partial class __default {
    public static Wrappers_Compile._IResult<Signature._ISignatureKeyPair, Dafny.Aws.Cryptography.Primitives.Types._IError> KeyGen(Signature._IECDSAParams s)
    {
      Wrappers_Compile._IResult<Signature._ISignatureKeyPair, Dafny.Aws.Cryptography.Primitives.Types._IError> res = Wrappers_Compile.Result<Signature._ISignatureKeyPair, Dafny.Aws.Cryptography.Primitives.Types._IError>.Default(Signature.SignatureKeyPair.Default());
      Signature._ISignatureKeyPair _117_sigKeyPair;
      Wrappers_Compile._IResult<Signature._ISignatureKeyPair, Dafny.Aws.Cryptography.Primitives.Types._IError> _118_valueOrError0 = Wrappers_Compile.Result<Signature._ISignatureKeyPair, Dafny.Aws.Cryptography.Primitives.Types._IError>.Default(Signature.SignatureKeyPair.Default());
      Wrappers_Compile._IResult<Signature._ISignatureKeyPair, Dafny.Aws.Cryptography.Primitives.Types._IError> _out10;
      _out10 = Signature.ECDSA.ExternKeyGen(s);
      _118_valueOrError0 = _out10;
      if ((_118_valueOrError0).IsFailure()) {
        res = (_118_valueOrError0).PropagateFailure<Signature._ISignatureKeyPair>();
        return res;
      }
      _117_sigKeyPair = (_118_valueOrError0).Extract();
      if ((new BigInteger(((_117_sigKeyPair).dtor_verificationKey).Count)) == ((s).FieldSize())) {
        res = Wrappers_Compile.Result<Signature._ISignatureKeyPair, Dafny.Aws.Cryptography.Primitives.Types._IError>.create_Success(_117_sigKeyPair);
        return res;
      } else {
        res = Wrappers_Compile.Result<Signature._ISignatureKeyPair, Dafny.Aws.Cryptography.Primitives.Types._IError>.create_Failure(Dafny.Aws.Cryptography.Primitives.Types.Error.create_AwsCryptographicPrimitivesError(Dafny.Sequence<char>.FromString("Incorrect verification-key length from ExternKeyGen.")));
        return res;
      }
      return res;
    }
  }
} // end of namespace Signature
namespace WrappedHKDF_Compile {

  public partial class __default {
    public static Dafny.ISequence<byte> Extract(Dafny.Aws.Cryptography.Primitives.Types._IHkdfExtractInput input)
    {
      Dafny.ISequence<byte> prk = Dafny.Sequence<byte>.Empty;
      Dafny.Aws.Cryptography.Primitives.Types._IHkdfExtractInput _let_tmp_rhs3 = input;
      Dafny.Aws.Cryptography.Primitives.Types._IDigestAlgorithm _119_digestAlgorithm = _let_tmp_rhs3.dtor_digestAlgorithm;
      Wrappers_Compile._IOption<Dafny.ISequence<byte>> _120_salt = _let_tmp_rhs3.dtor_salt;
      Dafny.ISequence<byte> _121_ikm = _let_tmp_rhs3.dtor_ikm;
      HMAC.HMac _122_hmac;
      HMAC.HMac _nw4 = new HMAC.HMac(_119_digestAlgorithm);
      _122_hmac = _nw4;
      Dafny.ISequence<byte> _out11;
      _out11 = HKDF_Compile.__default.Extract(_122_hmac, Wrappers_Compile.Option<Dafny.ISequence<byte>>.UnwrapOr(_120_salt, StandardLibrary_Compile.__default.Fill<byte>(0, Digest_Compile.__default.Length(_119_digestAlgorithm))), _121_ikm);
      prk = _out11;
      return prk;
    }
    public static Dafny.ISequence<byte> Expand(Dafny.Aws.Cryptography.Primitives.Types._IHkdfExpandInput input)
    {
      Dafny.ISequence<byte> okm = Dafny.Sequence<byte>.Empty;
      Dafny.Aws.Cryptography.Primitives.Types._IHkdfExpandInput _let_tmp_rhs4 = input;
      Dafny.Aws.Cryptography.Primitives.Types._IDigestAlgorithm _123_digestAlgorithm = _let_tmp_rhs4.dtor_digestAlgorithm;
      Dafny.ISequence<byte> _124_prk = _let_tmp_rhs4.dtor_prk;
      Dafny.ISequence<byte> _125_info = _let_tmp_rhs4.dtor_info;
      int _126_expectedLength = _let_tmp_rhs4.dtor_expectedLength;
      HMAC.HMac _127_hmac;
      HMAC.HMac _nw5 = new HMAC.HMac(_123_digestAlgorithm);
      _127_hmac = _nw5;
      Dafny.ISequence<byte> _128_output;
      Dafny.ISequence<byte> _out12;
      _out12 = HKDF_Compile.__default.Expand(_127_hmac, _124_prk, _125_info, new BigInteger(_126_expectedLength), _123_digestAlgorithm);
      _128_output = _out12;
      return okm;
    }
    public static Dafny.ISequence<byte> Hkdf(Dafny.Aws.Cryptography.Primitives.Types._IHkdfInput input)
    {
      Dafny.ISequence<byte> okm = Dafny.Sequence<byte>.Empty;
      Dafny.Aws.Cryptography.Primitives.Types._IHkdfInput _let_tmp_rhs5 = input;
      Dafny.Aws.Cryptography.Primitives.Types._IDigestAlgorithm _129_digest = _let_tmp_rhs5.dtor_digestAlgorithm;
      Wrappers_Compile._IOption<Dafny.ISequence<byte>> _130_salt = _let_tmp_rhs5.dtor_salt;
      Dafny.ISequence<byte> _131_ikm = _let_tmp_rhs5.dtor_ikm;
      Dafny.ISequence<byte> _132_info = _let_tmp_rhs5.dtor_info;
      int _133_expectedLength = _let_tmp_rhs5.dtor_expectedLength;
      Dafny.ISequence<byte> _out13;
      _out13 = HKDF_Compile.__default.Hkdf(_129_digest, _130_salt, _131_ikm, _132_info, new BigInteger(_133_expectedLength));
      okm = _out13;
      return okm;
    }
  }
} // end of namespace WrappedHKDF_Compile
namespace WrappedHMAC_Compile {

  public partial class __default {
    public static Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.Aws.Cryptography.Primitives.Types._IError> Digest(Dafny.Aws.Cryptography.Primitives.Types._IHMacInput input)
    {
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.Aws.Cryptography.Primitives.Types._IError> output = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.Aws.Cryptography.Primitives.Types._IError>.Default(Dafny.Sequence<byte>.Empty);
      Dafny.Aws.Cryptography.Primitives.Types._IHMacInput _let_tmp_rhs6 = input;
      Dafny.Aws.Cryptography.Primitives.Types._IDigestAlgorithm _134_digestAlgorithm = _let_tmp_rhs6.dtor_digestAlgorithm;
      Dafny.ISequence<byte> _135_key = _let_tmp_rhs6.dtor_key;
      Dafny.ISequence<byte> _136_message = _let_tmp_rhs6.dtor_message;
      Wrappers_Compile._IOutcome<Dafny.Aws.Cryptography.Primitives.Types._IError> _137_valueOrError0 = Wrappers_Compile.Outcome<Dafny.Aws.Cryptography.Primitives.Types._IError>.Default();
      _137_valueOrError0 = Wrappers_Compile.__default.Need<Dafny.Aws.Cryptography.Primitives.Types._IError>((new BigInteger((_135_key).Count)).Sign == 1, Dafny.Aws.Cryptography.Primitives.Types.Error.create_AwsCryptographicPrimitivesError(Dafny.Sequence<char>.FromString("Key MUST NOT be 0 bytes.")));
      if ((_137_valueOrError0).IsFailure()) {
        output = (_137_valueOrError0).PropagateFailure<Dafny.ISequence<byte>>();
        return output;
      }
      Wrappers_Compile._IOutcome<Dafny.Aws.Cryptography.Primitives.Types._IError> _138_valueOrError1 = Wrappers_Compile.Outcome<Dafny.Aws.Cryptography.Primitives.Types._IError>.Default();
      _138_valueOrError1 = Wrappers_Compile.__default.Need<Dafny.Aws.Cryptography.Primitives.Types._IError>((new BigInteger((_136_message).Count)) < (StandardLibrary_mUInt_Compile.__default.INT32__MAX__LIMIT), Dafny.Aws.Cryptography.Primitives.Types.Error.create_AwsCryptographicPrimitivesError(Dafny.Sequence<char>.FromString("Message over INT32_MAX_LIMIT")));
      if ((_138_valueOrError1).IsFailure()) {
        output = (_138_valueOrError1).PropagateFailure<Dafny.ISequence<byte>>();
        return output;
      }
      HMAC.HMac _139_hmac;
      HMAC.HMac _nw6 = new HMAC.HMac(_134_digestAlgorithm);
      _139_hmac = _nw6;
      (_139_hmac).Init(_135_key);
      (_139_hmac).BlockUpdate(_136_message);
      Dafny.ISequence<byte> _140_value;
      Dafny.ISequence<byte> _out14;
      _out14 = (_139_hmac).GetResult();
      _140_value = _out14;
      output = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.Aws.Cryptography.Primitives.Types._IError>.create_Success(_140_value);
      return output;
      return output;
    }
  }
} // end of namespace WrappedHMAC_Compile
namespace Dafny.Aws.Cryptography.Primitives {

  public partial class AtomicPrimitivesClient : Dafny.Aws.Cryptography.Primitives.Types.IAwsCryptographicPrimitivesClient {
    public AtomicPrimitivesClient() {
      this._config = Dafny.Aws.Cryptography.Primitives.Types.CryptoConfig.Default();
    }
    public void __ctor(Dafny.Aws.Cryptography.Primitives.Types._ICryptoConfig config)
    {
      (this)._config = config;
    }
    public Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.Aws.Cryptography.Primitives.Types._IError> GenerateRandomBytes(Dafny.Aws.Cryptography.Primitives.Types._IGenerateRandomBytesInput input)
    {
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.Aws.Cryptography.Primitives.Types._IError> output = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.Aws.Cryptography.Primitives.Types._IError>.Default(Dafny.Sequence<byte>.Empty);
      Dafny.ISequence<byte> _141_value;
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.Aws.Cryptography.Primitives.Types._IError> _142_valueOrError0 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.Aws.Cryptography.Primitives.Types._IError>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.Aws.Cryptography.Primitives.Types._IError> _out15;
      _out15 = Random_Compile.__default.GenerateBytes((input).dtor_length);
      _142_valueOrError0 = _out15;
      if ((_142_valueOrError0).IsFailure()) {
        output = (_142_valueOrError0).PropagateFailure<Dafny.ISequence<byte>>();
        return output;
      }
      _141_value = (_142_valueOrError0).Extract();
      output = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.Aws.Cryptography.Primitives.Types._IError>.create_Success(_141_value);
      return output;
    }
    public Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.Aws.Cryptography.Primitives.Types._IError> Digest(Dafny.Aws.Cryptography.Primitives.Types._IDigestInput input)
    {
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.Aws.Cryptography.Primitives.Types._IError> output = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.Aws.Cryptography.Primitives.Types._IError>.Default(Dafny.Sequence<byte>.Empty);
      Dafny.ISequence<byte> _143_value;
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.Aws.Cryptography.Primitives.Types._IError> _144_valueOrError0 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.Aws.Cryptography.Primitives.Types._IError>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.Aws.Cryptography.Primitives.Types._IError> _out16;
      _out16 = Digest_Compile.__default.Digest(input);
      _144_valueOrError0 = _out16;
      if ((_144_valueOrError0).IsFailure()) {
        output = (_144_valueOrError0).PropagateFailure<Dafny.ISequence<byte>>();
        return output;
      }
      _143_value = (_144_valueOrError0).Extract();
      output = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.Aws.Cryptography.Primitives.Types._IError>.create_Success(_143_value);
      return output;
    }
    public Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.Aws.Cryptography.Primitives.Types._IError> HMac(Dafny.Aws.Cryptography.Primitives.Types._IHMacInput input)
    {
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.Aws.Cryptography.Primitives.Types._IError> output = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.Aws.Cryptography.Primitives.Types._IError>.Default(Dafny.Sequence<byte>.Empty);
      Dafny.ISequence<byte> _145_value;
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.Aws.Cryptography.Primitives.Types._IError> _146_valueOrError0 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.Aws.Cryptography.Primitives.Types._IError>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.Aws.Cryptography.Primitives.Types._IError> _out17;
      _out17 = WrappedHMAC_Compile.__default.Digest(input);
      _146_valueOrError0 = _out17;
      if ((_146_valueOrError0).IsFailure()) {
        output = (_146_valueOrError0).PropagateFailure<Dafny.ISequence<byte>>();
        return output;
      }
      _145_value = (_146_valueOrError0).Extract();
      output = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.Aws.Cryptography.Primitives.Types._IError>.create_Success(_145_value);
      return output;
    }
    public Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.Aws.Cryptography.Primitives.Types._IError> HkdfExtract(Dafny.Aws.Cryptography.Primitives.Types._IHkdfExtractInput input)
    {
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.Aws.Cryptography.Primitives.Types._IError> output = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.Aws.Cryptography.Primitives.Types._IError>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile._IOutcome<Dafny.Aws.Cryptography.Primitives.Types._IError> _147_valueOrError0 = Wrappers_Compile.Outcome<Dafny.Aws.Cryptography.Primitives.Types._IError>.Default();
      _147_valueOrError0 = Wrappers_Compile.__default.Need<Dafny.Aws.Cryptography.Primitives.Types._IError>(((((input).dtor_salt).is_None) || ((new BigInteger((((input).dtor_salt).dtor_value).Count)).Sign != 0)) && ((new BigInteger(((input).dtor_ikm).Count)) < (StandardLibrary_mUInt_Compile.__default.INT32__MAX__LIMIT)), Dafny.Aws.Cryptography.Primitives.Types.Error.create_AwsCryptographicPrimitivesError(Dafny.Sequence<char>.FromString("No.")));
      if ((_147_valueOrError0).IsFailure()) {
        output = (_147_valueOrError0).PropagateFailure<Dafny.ISequence<byte>>();
        return output;
      }
      Dafny.ISequence<byte> _148_value;
      Dafny.ISequence<byte> _out18;
      _out18 = WrappedHKDF_Compile.__default.Extract(input);
      _148_value = _out18;
      output = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.Aws.Cryptography.Primitives.Types._IError>.create_Success(_148_value);
      return output;
    }
    public Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.Aws.Cryptography.Primitives.Types._IError> HkdfExpand(Dafny.Aws.Cryptography.Primitives.Types._IHkdfExpandInput input)
    {
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.Aws.Cryptography.Primitives.Types._IError> output = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.Aws.Cryptography.Primitives.Types._IError>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile._IOutcome<Dafny.Aws.Cryptography.Primitives.Types._IError> _149_valueOrError0 = Wrappers_Compile.Outcome<Dafny.Aws.Cryptography.Primitives.Types._IError>.Default();
      _149_valueOrError0 = Wrappers_Compile.__default.Need<Dafny.Aws.Cryptography.Primitives.Types._IError>(((((BigInteger.One) <= (new BigInteger((input).dtor_expectedLength))) && ((new BigInteger((input).dtor_expectedLength)) <= ((new BigInteger(255)) * (Digest_Compile.__default.Length((input).dtor_digestAlgorithm))))) && ((new BigInteger(((input).dtor_info).Count)) < (StandardLibrary_mUInt_Compile.__default.INT32__MAX__LIMIT))) && ((Digest_Compile.__default.Length((input).dtor_digestAlgorithm)) == (new BigInteger(((input).dtor_prk).Count))), Dafny.Aws.Cryptography.Primitives.Types.Error.create_AwsCryptographicPrimitivesError(Dafny.Sequence<char>.FromString("No.")));
      if ((_149_valueOrError0).IsFailure()) {
        output = (_149_valueOrError0).PropagateFailure<Dafny.ISequence<byte>>();
        return output;
      }
      Dafny.ISequence<byte> _150_value;
      Dafny.ISequence<byte> _out19;
      _out19 = WrappedHKDF_Compile.__default.Expand(input);
      _150_value = _out19;
      output = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.Aws.Cryptography.Primitives.Types._IError>.create_Success(_150_value);
      return output;
    }
    public Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.Aws.Cryptography.Primitives.Types._IError> Hkdf(Dafny.Aws.Cryptography.Primitives.Types._IHkdfInput input)
    {
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.Aws.Cryptography.Primitives.Types._IError> output = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.Aws.Cryptography.Primitives.Types._IError>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile._IOutcome<Dafny.Aws.Cryptography.Primitives.Types._IError> _151_valueOrError0 = Wrappers_Compile.Outcome<Dafny.Aws.Cryptography.Primitives.Types._IError>.Default();
      _151_valueOrError0 = Wrappers_Compile.__default.Need<Dafny.Aws.Cryptography.Primitives.Types._IError>((((((new BigInteger((input).dtor_expectedLength)).Sign != -1) && ((new BigInteger((input).dtor_expectedLength)) <= ((new BigInteger(255)) * (Digest_Compile.__default.Length((input).dtor_digestAlgorithm))))) && ((((input).dtor_salt).is_None) || ((new BigInteger((((input).dtor_salt).dtor_value).Count)).Sign != 0))) && ((new BigInteger(((input).dtor_info).Count)) < (StandardLibrary_mUInt_Compile.__default.INT32__MAX__LIMIT))) && ((new BigInteger(((input).dtor_ikm).Count)) < (StandardLibrary_mUInt_Compile.__default.INT32__MAX__LIMIT)), Dafny.Aws.Cryptography.Primitives.Types.Error.create_AwsCryptographicPrimitivesError(Dafny.Sequence<char>.FromString("No.")));
      if ((_151_valueOrError0).IsFailure()) {
        output = (_151_valueOrError0).PropagateFailure<Dafny.ISequence<byte>>();
        return output;
      }
      Dafny.ISequence<byte> _152_value;
      Dafny.ISequence<byte> _out20;
      _out20 = WrappedHKDF_Compile.__default.Hkdf(input);
      _152_value = _out20;
      output = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.Aws.Cryptography.Primitives.Types._IError>.create_Success(_152_value);
      return output;
    }
    public Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.Aws.Cryptography.Primitives.Types._IError> AESDecrypt(Dafny.Aws.Cryptography.Primitives.Types._IAESDecryptInput input)
    {
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.Aws.Cryptography.Primitives.Types._IError> output = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.Aws.Cryptography.Primitives.Types._IError>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile._IOutcome<Dafny.Aws.Cryptography.Primitives.Types._IError> _153_valueOrError0 = Wrappers_Compile.Outcome<Dafny.Aws.Cryptography.Primitives.Types._IError>.Default();
      _153_valueOrError0 = Wrappers_Compile.__default.Need<Dafny.Aws.Cryptography.Primitives.Types._IError>((((new BigInteger(((input).dtor_key).Count)) == (new BigInteger(((input).dtor_encAlg).dtor_keyLength))) && ((new BigInteger(((input).dtor_iv).Count)) == (new BigInteger(((input).dtor_encAlg).dtor_ivLength)))) && ((new BigInteger(((input).dtor_authTag).Count)) == (new BigInteger(((input).dtor_encAlg).dtor_tagLength))), Dafny.Aws.Cryptography.Primitives.Types.Error.create_AwsCryptographicPrimitivesError(Dafny.Sequence<char>.FromString("Request does not match algorithm.")));
      if ((_153_valueOrError0).IsFailure()) {
        output = (_153_valueOrError0).PropagateFailure<Dafny.ISequence<byte>>();
        return output;
      }
      Dafny.ISequence<byte> _154_value;
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.Aws.Cryptography.Primitives.Types._IError> _155_valueOrError1 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.Aws.Cryptography.Primitives.Types._IError>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.Aws.Cryptography.Primitives.Types._IError> _out21;
      _out21 = AESEncryption.__default.AESDecrypt(input);
      _155_valueOrError1 = _out21;
      if ((_155_valueOrError1).IsFailure()) {
        output = (_155_valueOrError1).PropagateFailure<Dafny.ISequence<byte>>();
        return output;
      }
      _154_value = (_155_valueOrError1).Extract();
      output = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.Aws.Cryptography.Primitives.Types._IError>.create_Success(_154_value);
      return output;
    }
    public Wrappers_Compile._IResult<Dafny.Aws.Cryptography.Primitives.Types._IAESEncryptOutput, Dafny.Aws.Cryptography.Primitives.Types._IError> AESEncrypt(Dafny.Aws.Cryptography.Primitives.Types._IAESEncryptInput input)
    {
      Wrappers_Compile._IResult<Dafny.Aws.Cryptography.Primitives.Types._IAESEncryptOutput, Dafny.Aws.Cryptography.Primitives.Types._IError> output = Wrappers_Compile.Result<Dafny.Aws.Cryptography.Primitives.Types._IAESEncryptOutput, Dafny.Aws.Cryptography.Primitives.Types._IError>.Default(Dafny.Aws.Cryptography.Primitives.Types.AESEncryptOutput.Default());
      Wrappers_Compile._IOutcome<Dafny.Aws.Cryptography.Primitives.Types._IError> _156_valueOrError0 = Wrappers_Compile.Outcome<Dafny.Aws.Cryptography.Primitives.Types._IError>.Default();
      _156_valueOrError0 = Wrappers_Compile.__default.Need<Dafny.Aws.Cryptography.Primitives.Types._IError>(((new BigInteger(((input).dtor_iv).Count)) == (new BigInteger(((input).dtor_encAlg).dtor_ivLength))) && ((new BigInteger(((input).dtor_key).Count)) == (new BigInteger(((input).dtor_encAlg).dtor_keyLength))), Dafny.Aws.Cryptography.Primitives.Types.Error.create_AwsCryptographicPrimitivesError(Dafny.Sequence<char>.FromString("Request does not match algorithm.")));
      if ((_156_valueOrError0).IsFailure()) {
        output = (_156_valueOrError0).PropagateFailure<Dafny.Aws.Cryptography.Primitives.Types._IAESEncryptOutput>();
        return output;
      }
      Dafny.Aws.Cryptography.Primitives.Types._IAESEncryptOutput _157_value;
      Wrappers_Compile._IResult<Dafny.Aws.Cryptography.Primitives.Types._IAESEncryptOutput, Dafny.Aws.Cryptography.Primitives.Types._IError> _158_valueOrError1 = Wrappers_Compile.Result<Dafny.Aws.Cryptography.Primitives.Types._IAESEncryptOutput, Dafny.Aws.Cryptography.Primitives.Types._IError>.Default(Dafny.Aws.Cryptography.Primitives.Types.AESEncryptOutput.Default());
      Wrappers_Compile._IResult<Dafny.Aws.Cryptography.Primitives.Types._IAESEncryptOutput, Dafny.Aws.Cryptography.Primitives.Types._IError> _out22;
      _out22 = AESEncryption.__default.AESEncrypt(input);
      _158_valueOrError1 = _out22;
      if ((_158_valueOrError1).IsFailure()) {
        output = (_158_valueOrError1).PropagateFailure<Dafny.Aws.Cryptography.Primitives.Types._IAESEncryptOutput>();
        return output;
      }
      _157_value = (_158_valueOrError1).Extract();
      output = Wrappers_Compile.Result<Dafny.Aws.Cryptography.Primitives.Types._IAESEncryptOutput, Dafny.Aws.Cryptography.Primitives.Types._IError>.create_Success(_157_value);
      return output;
    }
    public  Dafny.Aws.Cryptography.Primitives.Types._ICryptoConfig _config {get; set;}
    public Dafny.Aws.Cryptography.Primitives.Types._ICryptoConfig config { get {
      return this._config;
    } }
  }

  public partial class __default {
    public static Dafny.Aws.Cryptography.Primitives.Types._ICryptoConfig DefaultCryptoConfig() {
      return Dafny.Aws.Cryptography.Primitives.Types.CryptoConfig.create();
    }
    public static Wrappers_Compile._IResult<Dafny.Aws.Cryptography.Primitives.Types.IAwsCryptographicPrimitivesClient, Dafny.Aws.Cryptography.Primitives.Types._IError> Crypto(Dafny.Aws.Cryptography.Primitives.Types._ICryptoConfig config)
    {
      Wrappers_Compile._IResult<Dafny.Aws.Cryptography.Primitives.Types.IAwsCryptographicPrimitivesClient, Dafny.Aws.Cryptography.Primitives.Types._IError> res = default(Wrappers_Compile._IResult<Dafny.Aws.Cryptography.Primitives.Types.IAwsCryptographicPrimitivesClient, Dafny.Aws.Cryptography.Primitives.Types._IError>);
      Dafny.Aws.Cryptography.Primitives.AtomicPrimitivesClient _159_client;
      Dafny.Aws.Cryptography.Primitives.AtomicPrimitivesClient _nw7 = new Dafny.Aws.Cryptography.Primitives.AtomicPrimitivesClient();
      _nw7.__ctor(config);
      _159_client = _nw7;
      res = Wrappers_Compile.Result<Dafny.Aws.Cryptography.Primitives.AtomicPrimitivesClient, Dafny.Aws.Cryptography.Primitives.Types._IError>.create_Success(_159_client);
      return res;
      return res;
    }
  }
} // end of namespace Dafny.Aws.Cryptography.Primitives
namespace Aws_mCryptography_Compile {

} // end of namespace Aws_mCryptography_Compile
namespace Aws_Compile {

} // end of namespace Aws_Compile
namespace _module {

} // end of namespace _module
