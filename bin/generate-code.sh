#!/bin/bash

# A simple script for using our Polymorph package to generate
# all relevant code

if [ $# != 1 ] ; then
    echo "Please provide root directory of polymorph"
    exit 1
fi

pushd .

export POLYMORPH_ROOT=$1
export DAFNY_ROOT=`pwd`
export DOTNET_ROOT=$DAFNY_ROOT/aws-encryption-sdk-net

export ESDK_ROOT=$DAFNY_ROOT/src/SDK
export MaterialProviders_ROOT=$DAFNY_ROOT/src/AwsCryptographicMaterialProviders
export Crypto_ROOT=$DAFNY_ROOT/src/Crypto
export AWS_KMS_ROOT=$DAFNY_ROOT/src/AWS-KMS


cd "$POLYMORPH_ROOT"

# # Generate code for the AWS KMS SDK
./gradlew run --args="\
    --output-dotnet $AWS_KMS_ROOT/runtimes/net/Source/Generated/ \
    --model $AWS_KMS_ROOT/Model \
    --dependent-model $DAFNY_ROOT/model \
    --namespace com.amazonaws.kms \
    --aws-sdk"

# Generate code for cryptographic primitives
./gradlew run --args="\
    --output-dotnet $Crypto_ROOT/runtimes/net/Generated/ \
    --model $Crypto_ROOT/Model \
    --dependent-model $DAFNY_ROOT/model \
    --namespace aws.cryptography.primitives"

# Generate code for material providers
./gradlew run --args="\
    --output-dotnet $DOTNET_ROOT/Source/API/Generated/Crypto \
    --model $MaterialProviders_ROOT/Model \
    --dependent-model $AWS_KMS_ROOT/Model \
    --dependent-model $DAFNY_ROOT/model \
    --dependent-model $Crypto_ROOT/Model \
    --namespace aws.cryptography.materialProviders"

# # # Generate code for ESDK
# ./gradlew run --args="\
#     --output-dotnet $DOTNET_ROOT/Source/API/Generated/Esdk \
#     --model $ESDK_ROOT/Model \
#     --dependent-model $MaterialProviders_ROOT/Model \
#     --dependent-model $DAFNY_ROOT/model \
#     --dependent-model $AWS_KMS_ROOT/Model \
#     --dependent-model $Crypto_ROOT/Model \
#     --namespace aws.encryptionSdk"

popd
