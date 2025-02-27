// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.

using System;
using AWS.EncryptionSDK.Core;

namespace AWS.EncryptionSDK.Core
{
    public class OnEncryptInput
    {
        private AWS.EncryptionSDK.Core.EncryptionMaterials _materials;

        public AWS.EncryptionSDK.Core.EncryptionMaterials Materials
        {
            get { return this._materials; }
            set { this._materials = value; }
        }

        internal bool IsSetMaterials()
        {
            return this._materials != null;
        }

        public void Validate()
        {
            if (!IsSetMaterials())
                throw new System.ArgumentException("Missing value for required property 'Materials'");
        }
    }
}
