// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.

using System;
using System.IO;
using System.Collections.Generic;
using AWS.EncryptionSDK.Core;

namespace AWS.EncryptionSDK.Core
{
    public static class AwsCryptographicMaterialProvidersFactory
    {
        static readonly
            Dafny.Aws.EncryptionSdk.Core.AwsCryptographicMaterialProvidersFactory.
            AwsCryptographicMaterialProvidersFactory _impl =
                new Dafny.Aws.EncryptionSdk.Core.AwsCryptographicMaterialProvidersFactory.
                    AwsCryptographicMaterialProvidersFactory();

        public static AWS.EncryptionSDK.Core.IAwsCryptographicMaterialProviders
            CreateDefaultAwsCryptographicMaterialProviders()
        {
            Wrappers_Compile._IResult<Dafny.Aws.EncryptionSdk.Core.IAwsCryptographicMaterialProviders,
                Dafny.Aws.EncryptionSdk.Core.IAwsCryptographicMaterialProvidersException> result =
                _impl.CreateDefaultAwsCryptographicMaterialProviders();
            if (result.is_Failure)
                throw TypeConversion.FromDafny_CommonError_AwsCryptographicMaterialProvidersBaseException(
                    result.dtor_error);
            return TypeConversion
                .FromDafny_N3_aws__N13_encryptionSdk__N4_core__S42_AwsCryptographicMaterialProvidersReference(
                    result.dtor_value);
        }
    }
}
