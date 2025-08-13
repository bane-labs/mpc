# mpc

This is a repository for Neo X ZK-DKG MPC ceremony, please refer [bane-labs/zk-dkg](https://github.com/bane-labs/zk-dkg) about the tool and [neo-x-mpc](https://github.com/bane-labs/zk-dkg/blob/main/neo-x-mpc.md) about the steps.

## Information

|Name              |Property                                    |
|------------------|--------------------------------------------|
|Proof System      |Groth16                                     |
|Power of Tau      |2^24                                        |
|Number of Circuits|3                                           |
|NeoFS Network     |Mainnet                                     |
|NeoFS Container   |411d8vuzogogMxXJqTQcu61btgQ6rL2VNYUYnH7r4kE3|

NGD is responsible for phase initialization and sealing, so we expect the contribution order to be **NGD=>NSPCC=>AxLabs=>lazynode**.

## How to Contribute

Please contribute the MPC file according to the order, upload the result through NeoFS, and provide following information through **pull request**:

1. Result file challenge, you can get it from the `zk-dkg` command line output after computation;
2. NeoFS object ID, you can get it from the `neofs-cli` command line output after file upload.

After all of the MPC contributions, NGD will backup the results to cloud, so please leave the `Cloud URL` field as empty in pull requests.

## Phase1 Attestations

|Participant|File Challenge                                                  |NeoFS Object ID                             |Cloud URL                                                        |
|-----------|----------------------------------------------------------------|--------------------------------------------|-----------------------------------------------------------------|
|NGD        |071d2176b99861f97e57020cd5ef3904299fffb1fdb8bf0994d9bbf5e36f60ad|4t51oBmnwu3UHpC35HAS3aoF2jcMtjmpL9df7vZR447r|https://zkstorage.blob.core.windows.net/zk-blob/Phase1_1_NGD     |
|NSPCC      |3446c3cc02a91df93846621f7b9d3641ca2638a0c959e2b5e03bc37823f27625|4QNXbGzU3ooJgpsR7EVawyKgtrQSDDw5BwdLYeND9gZT|https://zkstorage.blob.core.windows.net/zk-blob/Phase1_2_NSPCC   |
|AxLabs     |4a7b705174f35e07672dbf3271cb2dfe2948b2861df4b7e98fece41fe8c3f21e|CpbUnRe4qnxQZQH1SrKqCuCXo8aBis4HsuKDeN2ghB6w|https://zkstorage.blob.core.windows.net/zk-blob/Phase1_3_AxLabs  |
|lazynode   |2a9d15f8d5dbf0117b4cbb7fd43f41ccd1be3c9409e3d6f7da4964aa6447547c|8q5JMQ6x3ELp2XkLeqtGpGGHEiqgvRXL4a6AyHHvobi2|https://zkstorage.blob.core.windows.net/zk-blob/Phase1_4_lazynode|

The beacon challenge for sealing: `0000000000000000000083db7a400c903dd45b4a073f645d8c4420170a69eac8` (Hash of Bitcoin [#909534](https://btcscan.org/block/0000000000000000000083db7a400c903dd45b4a073f645d8c4420170a69eac8)).

#### Sealed SRS

|File Checksum                                                   |NeoFS Object ID                             |Cloud URL                                                         |
|----------------------------------------------------------------|--------------------------------------------|------------------------------------------------------------------|
|1a1f5d0928659170b925d7b681756b82ecade7fa61877042b69e6680a25c53ff|H9i8kUoujytHrsGBRpfWc91M1fE7KnptvFAVgx6nFRx9|https://zkstorage.blob.core.windows.net/zk-blob/Phase1_seal_result|

## Phase2 Attestations

### Circuit 1 (1-Message)

|Participant|File Challenge                                                  |NeoFS Object ID                             |Cloud URL|
|-----------|----------------------------------------------------------------|--------------------------------------------|---------|
|NGD        |1e94c91b881eda204fb19f62052feb111ca413abf4222fb4ae46b7af4badb557|9nZsqb8n3VsjzKWotU8J3gKivsjpBV9MKMdMdpczdZgR|         |
|NSPCC      |                                                                |                                            |         |
|AxLabs     |                                                                |                                            |         |
|lazynode   |                                                                |                                            |         |

### Circuit 2 (2-Message)

|Participant|File Challenge                                                  |NeoFS Object ID                             |Cloud URL|
|-----------|----------------------------------------------------------------|--------------------------------------------|---------|
|NGD        |ce58359d13e4db9ec16ae19666e0e3b2b9ae252bf695207bcb15349a50cf3f19|DHBCUUaCEoQnxu9VFSPoprfTLqhSKKe9yf2sjFgz8Kat|         |
|NSPCC      |                                                                |                                            |         |
|AxLabs     |                                                                |                                            |         |
|lazynode   |                                                                |                                            |         |

### Circuit 3 (7-Message)

|Participant|File Challenge                                                  |NeoFS Object ID                             |Cloud URL|
|-----------|----------------------------------------------------------------|--------------------------------------------|---------|
|NGD        |5cc93a1eec5e77380d915abfad18f531071dd809acbf665bdb08b602f463e821|96x52Scb6iidhUJE1YMCMzCUUbzHqqxriqBmp8Jh2smV|         |
|NSPCC      |                                                                |                                            |         |
|AxLabs     |                                                                |                                            |         |
|lazynode   |                                                                |                                            |         |

The beacon challenge for sealing: 
