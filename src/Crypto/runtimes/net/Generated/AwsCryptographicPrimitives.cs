// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using System.IO;
 using System.Collections.Generic;
 using AWS.Cryptography.Primitives;
 using Dafny.Aws.Cryptography.Primitives.Types; namespace AWS.Cryptography.Primitives {
 public class AwsCryptographicPrimitives {
 internal readonly IAwsCryptographicPrimitivesClient _impl;
 internal AwsCryptographicPrimitives(IAwsCryptographicPrimitivesClient impl) { this._impl = impl; }
 public System.IO.MemoryStream GenerateRandomBytes(AWS.Cryptography.Primitives.GenerateRandomBytesInput input) {
 Dafny.Aws.Cryptography.Primitives.Types._IGenerateRandomBytesInput internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N10_primitives__S24_GenerateRandomBytesInput(input);
 Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.Aws.Cryptography.Primitives.Types._IError> result = _impl.GenerateRandomBytes(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError_AwsCryptographicPrimitivesBaseException(result.dtor_error);
 return TypeConversion.FromDafny_N3_aws__N12_cryptography__N10_primitives__S25_GenerateRandomBytesOutput(result.dtor_value);
}
 public System.IO.MemoryStream Digest(AWS.Cryptography.Primitives.DigestInput input) {
 Dafny.Aws.Cryptography.Primitives.Types._IDigestInput internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N10_primitives__S11_DigestInput(input);
 Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.Aws.Cryptography.Primitives.Types._IError> result = _impl.Digest(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError_AwsCryptographicPrimitivesBaseException(result.dtor_error);
 return TypeConversion.FromDafny_N3_aws__N12_cryptography__N10_primitives__S12_DigestOutput(result.dtor_value);
}
 public System.IO.MemoryStream HMac(AWS.Cryptography.Primitives.HMacInput input) {
 Dafny.Aws.Cryptography.Primitives.Types._IHMacInput internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N10_primitives__S9_HMacInput(input);
 Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.Aws.Cryptography.Primitives.Types._IError> result = _impl.HMac(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError_AwsCryptographicPrimitivesBaseException(result.dtor_error);
 return TypeConversion.FromDafny_N3_aws__N12_cryptography__N10_primitives__S10_HMacOutput(result.dtor_value);
}
 public System.IO.MemoryStream HkdfExtract(AWS.Cryptography.Primitives.HkdfExtractInput input) {
 Dafny.Aws.Cryptography.Primitives.Types._IHkdfExtractInput internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N10_primitives__S16_HkdfExtractInput(input);
 Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.Aws.Cryptography.Primitives.Types._IError> result = _impl.HkdfExtract(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError_AwsCryptographicPrimitivesBaseException(result.dtor_error);
 return TypeConversion.FromDafny_N3_aws__N12_cryptography__N10_primitives__S17_HkdfExtractOutput(result.dtor_value);
}
 public System.IO.MemoryStream HkdfExpand(AWS.Cryptography.Primitives.HkdfExpandInput input) {
 Dafny.Aws.Cryptography.Primitives.Types._IHkdfExpandInput internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N10_primitives__S15_HkdfExpandInput(input);
 Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.Aws.Cryptography.Primitives.Types._IError> result = _impl.HkdfExpand(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError_AwsCryptographicPrimitivesBaseException(result.dtor_error);
 return TypeConversion.FromDafny_N3_aws__N12_cryptography__N10_primitives__S16_HkdfExpandOutput(result.dtor_value);
}
 public System.IO.MemoryStream Hkdf(AWS.Cryptography.Primitives.HkdfInput input) {
 Dafny.Aws.Cryptography.Primitives.Types._IHkdfInput internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N10_primitives__S9_HkdfInput(input);
 Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.Aws.Cryptography.Primitives.Types._IError> result = _impl.Hkdf(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError_AwsCryptographicPrimitivesBaseException(result.dtor_error);
 return TypeConversion.FromDafny_N3_aws__N12_cryptography__N10_primitives__S10_HkdfOutput(result.dtor_value);
}
 public AWS.Cryptography.Primitives.AESEncryptOutput AESEncrypt(AWS.Cryptography.Primitives.AESEncryptInput input) {
 Dafny.Aws.Cryptography.Primitives.Types._IAESEncryptInput internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N10_primitives__S15_AESEncryptInput(input);
 Wrappers_Compile._IResult<Dafny.Aws.Cryptography.Primitives.Types._IAESEncryptOutput, Dafny.Aws.Cryptography.Primitives.Types._IError> result = _impl.AESEncrypt(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError_AwsCryptographicPrimitivesBaseException(result.dtor_error);
 return TypeConversion.FromDafny_N3_aws__N12_cryptography__N10_primitives__S16_AESEncryptOutput(result.dtor_value);
}
 public System.IO.MemoryStream AESDecrypt(AWS.Cryptography.Primitives.AESDecryptInput input) {
 Dafny.Aws.Cryptography.Primitives.Types._IAESDecryptInput internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N10_primitives__S15_AESDecryptInput(input);
 Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.Aws.Cryptography.Primitives.Types._IError> result = _impl.AESDecrypt(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError_AwsCryptographicPrimitivesBaseException(result.dtor_error);
 return TypeConversion.FromDafny_N3_aws__N12_cryptography__N10_primitives__S16_AESDecryptOutput(result.dtor_value);
}
}
}
