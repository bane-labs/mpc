# mpc

This is a repository for Neo X ZK-DKG MPC ceremony, please refer [bane-labs/zk-dkg](https://github.com/bane-labs/zk-dkg) about the tool and [neo-x-mpc](https://github.com/bane-labs/zk-dkg/blob/main/neo-x-mpc.md) about the steps.

## Information

|Name              |Property                                      |
|------------------|----------------------------------------------|
|Proof System      |`Groth16`                                     |
|Power of Tau      |`2^24`                                        |
|Number of Circuits|`3`                                           |
|NeoFS Network     |`Mainnet`                                     |
|NeoFS Container   |`411d8vuzogogMxXJqTQcu61btgQ6rL2VNYUYnH7r4kE3`|

NGD is responsible for phase initialization and sealing, so we expect the contribution order to be **NGD=>NSPCC=>AxLabs=>Lazynode**.

## How to Contribute

Please contribute the MPC file according to the order, upload the result through NeoFS, and provide following information through **pull request**:

1. Result file challenge, you can get it from the `zk-dkg` command line output after computation;
2. NeoFS object ID, you can get it from the `neofs-cli` command line output after file upload.

After all of the MPC contributions, NGD will backup the results to cloud, so please leave the `Cloud URL` field as empty in pull requests.

## Phase1 Attestations

|Participant|File Challenge                                                    |NeoFS Object ID                               |Cloud URL                                                        |
|-----------|------------------------------------------------------------------|----------------------------------------------|-----------------------------------------------------------------|
|NGD        |`071d2176b99861f97e57020cd5ef3904299fffb1fdb8bf0994d9bbf5e36f60ad`|`4t51oBmnwu3UHpC35HAS3aoF2jcMtjmpL9df7vZR447r`|https://zkstorage.blob.core.windows.net/zk-blob/Phase1_1_NGD     |
|NSPCC      |`3446c3cc02a91df93846621f7b9d3641ca2638a0c959e2b5e03bc37823f27625`|`4QNXbGzU3ooJgpsR7EVawyKgtrQSDDw5BwdLYeND9gZT`|https://zkstorage.blob.core.windows.net/zk-blob/Phase1_2_NSPCC   |
|AxLabs     |`4a7b705174f35e07672dbf3271cb2dfe2948b2861df4b7e98fece41fe8c3f21e`|`CpbUnRe4qnxQZQH1SrKqCuCXo8aBis4HsuKDeN2ghB6w`|https://zkstorage.blob.core.windows.net/zk-blob/Phase1_3_AxLabs  |
|Lazynode   |`2a9d15f8d5dbf0117b4cbb7fd43f41ccd1be3c9409e3d6f7da4964aa6447547c`|`8q5JMQ6x3ELp2XkLeqtGpGGHEiqgvRXL4a6AyHHvobi2`|https://zkstorage.blob.core.windows.net/zk-blob/Phase1_4_Lazynode|

The beacon challenge for sealing: `0000000000000000000083db7a400c903dd45b4a073f645d8c4420170a69eac8` (Hash of Bitcoin [#909534](https://btcscan.org/block/0000000000000000000083db7a400c903dd45b4a073f645d8c4420170a69eac8)).

#### Sealed SRS

|File Checksum                                                     |NeoFS Object ID                               |Cloud URL                                                         |
|------------------------------------------------------------------|----------------------------------------------|------------------------------------------------------------------|
|`1a1f5d0928659170b925d7b681756b82ecade7fa61877042b69e6680a25c53ff`|`H9i8kUoujytHrsGBRpfWc91M1fE7KnptvFAVgx6nFRx9`|https://zkstorage.blob.core.windows.net/zk-blob/Phase1_seal_result|

## Phase2 Attestations

### Circuit 1 (1-Message)

|Participant|File Challenge                                                    |NeoFS Object ID                               |Cloud URL                                                          |
|-----------|------------------------------------------------------------------|----------------------------------------------|-------------------------------------------------------------------|
|NGD        |`1e94c91b881eda204fb19f62052feb111ca413abf4222fb4ae46b7af4badb557`|`9nZsqb8n3VsjzKWotU8J3gKivsjpBV9MKMdMdpczdZgR`|https://zkstorage.blob.core.windows.net/zk-blob/Phase2_1_1_NGD     |
|NSPCC      |`8a4cf7eeedc3b1ad759152cf1102eac1f69ab58cc0f782e1acbdd7b4023688a3`|`BS1gXCsnwnXH3C9K9MS9Y8RA3NmdXHnaPZNjQx3eQe2Y`|https://zkstorage.blob.core.windows.net/zk-blob/Phase2_1_2_NSPCC   |
|AxLabs     |`538e6543b74b5239249fd35aa146ea892d3ee94700d6a225a7255c1917e09781`|`5BCRFC4B4iU4XPVsraVFyh69nphZHsZuLtrNhX6Rdn6j`|https://zkstorage.blob.core.windows.net/zk-blob/Phase2_1_3_AxLabs  |
|Lazynode   |`a4d1f805cc24c2ec4f01481cafea656c25fbe9f6464d4f6b636e060388951082`|`8xs2wdLiVywCid4Wt6tqQoCQVMT7dEiZJJF5tnpwNWFC`|https://zkstorage.blob.core.windows.net/zk-blob/Phase2_1_4_Lazynode|

### Circuit 2 (2-Message)

|Participant|File Challenge                                                    |NeoFS Object ID                               |Cloud URL                                                          |
|-----------|------------------------------------------------------------------|----------------------------------------------|-------------------------------------------------------------------|
|NGD        |`ce58359d13e4db9ec16ae19666e0e3b2b9ae252bf695207bcb15349a50cf3f19`|`DHBCUUaCEoQnxu9VFSPoprfTLqhSKKe9yf2sjFgz8Kat`|https://zkstorage.blob.core.windows.net/zk-blob/Phase2_2_1_NGD     |
|NSPCC      |`255f35b1e50849506b37ec4de84038e797fde031c600b39f9a5737ba26edf89f`|`3Wu65swwiSKHZVPLRouDUC1atQ556uGcDiekwAa7vThE`|https://zkstorage.blob.core.windows.net/zk-blob/Phase2_2_2_NSPCC   |
|AxLabs     |`59332f836c5c370aa4415cac1a9b4be33040db77fb26abe689ed515a319ea448`|`4qRpGkdjfkcWkKRSjM2R859FG86zNNCN5b9P6yZpsFGK`|https://zkstorage.blob.core.windows.net/zk-blob/Phase2_2_3_AxLabs  |
|Lazynode   |`3ac9d298e0f5d7889db486447f72439effbd026e7b446bfa537edff256992488`|`58ttsLQa9moUzULoNjggEYqucDbjPBYwv7L5fkv8pSSa`|https://zkstorage.blob.core.windows.net/zk-blob/Phase2_2_4_Lazynode|

### Circuit 3 (7-Message)

|Participant|File Challenge                                                    |NeoFS Object ID                               |Cloud URL                                                          |
|-----------|------------------------------------------------------------------|----------------------------------------------|-------------------------------------------------------------------|
|NGD        |`5cc93a1eec5e77380d915abfad18f531071dd809acbf665bdb08b602f463e821`|`96x52Scb6iidhUJE1YMCMzCUUbzHqqxriqBmp8Jh2smV`|https://zkstorage.blob.core.windows.net/zk-blob/Phase2_3_1_NGD     |
|NSPCC      |`740fec9efcb667b4b92b9dda363de11ae54c3377f5b64dd08e05247eaedf22e5`|`6b4HEzEibnHyhEKGPSswq64xi584dhofEpQEmZBmaphJ`|https://zkstorage.blob.core.windows.net/zk-blob/Phase2_3_2_NSPCC   |
|AxLabs     |`333ddd24656c1327330bec9ef5088e3d88af6beac0804a77bf050dae29800d0d`|`8Xt2oo9LbvzHeBK7MRyja4MjJtpu1u4N6eaB1sHRsTRy`|https://zkstorage.blob.core.windows.net/zk-blob/Phase2_3_3_AxLabs  |
|Lazynode   |`8d56faadb8e47ccfb2f87cbba48a8f61f4675ae287051e87a68a3da61fe1e6d6`|`5vDCeTE7ynv5ydL17MmRrj9rWsrNy44Me1LHBvxuFtGR`|https://zkstorage.blob.core.windows.net/zk-blob/Phase2_3_4_Lazynode|

The beacon challenge for sealing: `00000000000000000000e6bc740876482860c26a196769875c00edeaeeefff20` (Hash of Bitcoin [#909992](https://btcscan.org/block/00000000000000000000e6bc740876482860c26a196769875c00edeaeeefff20)).

#### Seal result

|Exported Name|File Checksum                                                     |NeoFS Object ID                               |Cloud URL                                                        |
|-------------|------------------------------------------------------------------|----------------------------------------------|-----------------------------------------------------------------|
|1-Message CCS|`08741f3db4a34f98804c33cc3b719cd6842cc2a433382de020a371999f5be3ae`|`8f6m4RUvgNDyo7gdFhEJQEAqkdaTzEj4oYuLVxfRJP4S`|https://zkstorage.blob.core.windows.net/zk-blob/one_message.ccs  |
|2-Message CCS|`53d26dba85f5e8d18af471cfccc9aa86eabe758ed3fae28524d4f7b406d76289`|`Fqzn6PvAhmmYWVBRV8dVRWwAL3T8JHgycBfjS7A18z6f`|https://zkstorage.blob.core.windows.net/zk-blob/two_message.ccs  |
|7-Message CCS|`bcad0a7c3c6005e283daf4baa2af3d74dde3a0fb08713df14ae1772e30cfaa2b`|`2jNd8acKHBb5s6matnED49MCo36vTMWXbfjocT7Xcub7`|https://zkstorage.blob.core.windows.net/zk-blob/seven_message.ccs|

|Exported Name|File Checksum                                                     |NeoFS Object ID                               |Cloud URL                                                       |
|-------------|------------------------------------------------------------------|----------------------------------------------|----------------------------------------------------------------|
|1-Message PK |`3d470a6e43570f2c8d171e299a384749809b5211bc1af0710f6d45b56ec69373`|`HZVzrU7348zztWvgBTM3xkpvZ6BNNJMGDrKyeDDTHZLw`|https://zkstorage.blob.core.windows.net/zk-blob/one_message.pk  |
|2-Message PK |`1d92851d68e8d7787656ceaaa1241c3d5aee29ce8396b22b1eaa4cffeeb442cc`|`HKEeCskBjnL5yJGXYP4EfakVaDsw3aAJ64FXavDhpv4E`|https://zkstorage.blob.core.windows.net/zk-blob/two_message.pk  |
|7-Message PK |`39fbe9b2c54be6a150a05b598875c220894b8580e202a343d7974e133b6eca10`|`A1DTHYvdnzrgEJP14yzt2T8AXsuM3YaNDoe3LoMWXepT`|https://zkstorage.blob.core.windows.net/zk-blob/seven_message.pk|

|Exported Name|Value                                     |Verifier Contract                                               |
|-------------|------------------------------------------|----------------------------------------------------------------|
|1-Message VK |[one_message.vk](./vks/one_message.vk)    |[OneMessageVerifier.sol](./contracts/OneMessageVerifier.sol)    |
|2-Message VK |[two_message.vk](./vks/two_message.vk)    |[TwoMessageVerifier.sol](./contracts/TwoMessageVerifier.sol)    |
|7-Message VK |[seven_message.vk](./vks/seven_message.vk)|[SevenMessageVerifier.sol](./contracts/SevenMessageVerifier.sol)|
