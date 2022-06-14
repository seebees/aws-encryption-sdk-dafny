// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Model/ComAmazonawsKmsTypes.dfy"

module {:extern "Com.Amazonaws.Kms"} Com.Amazonaws.Kms {

 import opened Wrappers
 import opened StandardLibrary.UInt
 import opened UTF8
 import opened Types = ComAmazonawsKmsTypes
 datatype KMSClientConfigType = KMSClientConfigType
//  function method DefaultKMSClientConfigType(): KMSClientConfigType
 method {:extern} KMSClient()
 returns (res: Result<IKeyManagementServiceClient, Error>)

  function method DefaultKMSClientConfigType() : KMSClientConfigType {
    KMSClientConfigType
  }

}
