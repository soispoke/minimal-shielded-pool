// SPDX-License-Identifier: Apache-2.0
pragma solidity ^0.8.24;

/// @title ShieldedPoolLogic
/// @notice The minimal shielded pool's state and its state-changing entry points: shield,
/// settle, publishEpochRoot and claimWithdrawal. It runs only through the dispatcher
/// (core/dispatcher/ShieldedPoolDispatcher.yul), which delegatecalls every call except its
/// own VERIFY entry, so the state lives in the dispatcher's storage.
/// @dev The dispatcher checks a spend's proof and whole frame transaction before approving
/// it, and approval consumes the spend's nullifiers. A settlement that then fails burns the
/// notes, so every refusal in settle is also made before approval (see settle).
contract ShieldedPoolLogic {
    /// @notice The depth of each epoch's Merkle tree, as in the circuit.
    uint32 public constant DEPTH = 20;
    uint32 public constant CAPACITY = uint32(1) << DEPTH;
    /// @dev BN254's scalar field order p, the circuit's field.
    uint256 internal constant P = 21888242871839275222246405745257275088548364400416034343698204186575808495617;
    /// @dev Amounts are below 2^128, the circuit's range check.
    uint256 internal constant MAX_VALUE = 1 << 128;
    /// @notice The root of the empty depth-20 tree, _zeros(DEPTH).
    bytes32 public constant EMPTY_ROOT = 0x2134e76ac5d21aab186c2be1dd8f84ee880a1e46eaf712f9d371b6df22191f3e;
    /// @notice keccak256("minimal-shielded-pool:occurrence-domain:v1"), the first word of
    /// every nullifier domain.
    bytes32 public constant DOMAIN_TAG = 0xa9d03fa1cd97bcf3294dc8e3bb024f555393c98967b356967fa502abab366ed3;
    /// @notice The first output's sink, Poseidon(2, 1, 0): the commitment a zero-value first
    /// output must have. Settlement does not insert sinks.
    bytes32 public constant SINK_0 = 0x23f1b896ada6ee5dac80945b11329e7ab64412c2be9f5c87cfa3261cc1d8216f;
    /// @notice The second output's sink, Poseidon(2, 2, 0).
    bytes32 public constant SINK_1 = 0x2fd476622c67c880b3049a76c7337192362834c9d6dfb55c5060bb96c98932bb;
    /// @notice EIP-8272's RECENT_ROOT_ADDRESS, which publishEpochRoot writes to.
    address public constant RECENT_ROOT_PREDEPLOY = address(0x8272);
    /// @notice A note is a 16-byte tag, a 16-byte encrypted amount and a 16-byte
    /// authentication tag. The pool publishes notes and never reads them: a wrong note only
    /// stops the recipient from finding its payment.
    uint256 public constant NOTE_BYTES = 48;
    /// @notice The length of the ML-KEM-768 ciphertext that a sender's first payment to a
    /// public address puts before its notes.
    uint256 public constant KEM_CIPHERTEXT_BYTES = 1088;
    /// @dev settle(Spend) calldata is the selector and twelve words; the notes follow.
    uint256 internal constant SETTLE_SPEND_BYTES = 4 + 12 * 32;

    address private immutable IMPLEMENTATION_SELF = address(this);
    address public immutable POSEIDON_T3;
    address public immutable POSEIDON_T4;

    // The dispatcher's constructor writes EMPTY_ROOT to slot 22, so these slots must not move.
    /// @notice The current tree's filled left subtrees by height (see _insert).
    bytes32[DEPTH + 1] public filledSubtrees; // slots 0..20
    /// @notice The number of leaves in the current tree, which is the next leaf's index.
    uint32 public nextIndex; // slot 21
    bytes32 public currentRoot; // slot 22
    /// @notice The ETH settlement owes each recipient, which claimWithdrawal pays out.
    mapping(address => uint256) public withdrawalCredit; // slot 23
    /// @notice The epoch whose tree takes new leaves.
    uint64 public currentEpoch; // slot 24
    /// @notice Each closed epoch's root, from when it closed.
    mapping(uint64 => bytes32) public finalRoot; // slot 25

    /// @dev settle's argument. The proof covers ten fields, in the statement order nf1, nf2,
    /// outCm1, outCm2, root, domain, publicAmount, fee, recipient, authorizer. rootSlot and
    /// epoch name the recent-root tuple, and the domain takes the same epoch.
    struct Spend {
        bytes32 root;
        uint64 rootSlot;
        uint64 epoch;
        bytes32 domain;
        bytes32 nf1;
        bytes32 nf2;
        bytes32 outCm1;
        bytes32 outCm2;
        uint256 publicAmount;
        uint256 fee;
        address recipient;
        address authorizer;
    }

    /// @notice A commitment was appended to the current epoch's tree.
    /// @param index Its leaf index in that tree, which its nullifier binds.
    /// @param newRoot The tree's root after every leaf this call appends, so both outputs of
    /// one settlement carry the same root.
    event LeafAppended(bytes32 indexed cm, uint64 indexed epoch, uint32 index, bytes32 newRoot);
    /// @notice A settled spend's nullifier, which approval consumed as an EIP-8250 nonce key.
    /// Wallets track their spends by it.
    event NoteSpent(bytes32 indexed nf);
    /// @notice The tree lacked room, so the pool closed an epoch and started an empty tree.
    /// @param finalRoot The closed epoch's root, which spends of its notes keep proving against.
    event EpochRolled(uint64 indexed closedEpoch, bytes32 finalRoot, uint64 indexed newEpoch);
    /// @notice The pool wrote an epoch's root to EIP-8272.
    event RootPublished(uint64 indexed epoch, bytes32 indexed source, bytes32 root);
    /// @notice A settlement credited a withdrawal, which claimWithdrawal pays out.
    event WithdrawalCredited(address indexed recipient, uint256 amount);
    /// @notice claimWithdrawal paid a recipient its whole credit.
    event Withdrawn(address indexed recipient, uint256 amount);
    /// @notice The encrypted notes a shield or settlement carries, as sent.
    /// @param notes One note for a shield or two for a settlement, optionally after an
    /// ML-KEM-768 ciphertext.
    event Notes(bytes notes);

    error DirectImplementationCall();
    error ZeroValueShield();
    /// @notice An amount is 2^128 or more, which no proof can spend.
    error ValueTooLarge();
    /// @notice A shield's commitment is a sink. A shield's value is never zero, so only a
    /// Poseidon collision reaches this.
    error ReservedSink();
    /// @notice A value that must be a field element is p or more.
    error NotCanonical();
    error NotPoolSender();
    error ZeroNullifier();
    /// @notice A spend's domain is not domain(epoch).
    error InvalidDomain();
    /// @notice The epoch is after the current one.
    error InvalidEpoch();
    error InvalidAuthorizer();
    /// @notice A spend names a recipient without a withdrawal or a withdrawal without a
    /// recipient, has two equal outputs, or has a sink in the other output's position.
    error InvalidSettlementShape();
    /// @notice The epoch has no root, which happens only if the pool's deployment did not
    /// store EMPTY_ROOT.
    error InvalidRoot();
    error RootPublishFailed();
    error NoCredit();
    /// @notice The ETH transfer to the recipient failed, so the credit stays.
    error PayoutFailed();
    error InvalidHashLibrary();
    /// @notice A Poseidon call failed or did not return one field element.
    error HashFailed();
    error InvalidNotes();

    /// @dev Refuses a call to the implementation itself, whose own storage is not the pool's.
    /// A direct shield, for one, would lock its ETH in the implementation.
    modifier onlyDelegate() {
        if (address(this) == IMPLEMENTATION_SELF) revert DirectImplementationCall();
        _;
    }

    /// @dev The dispatcher's constructor, not this one, stores EMPTY_ROOT in slot 22.
    constructor(address poseidonT3, address poseidonT4) {
        if (poseidonT3.code.length == 0 || poseidonT4.code.length == 0) revert InvalidHashLibrary();
        POSEIDON_T3 = poseidonT3;
        POSEIDON_T4 = poseidonT4;
    }

    /// @notice The EIP-8272 source_id that publishEpochRoot(epoch) writes under,
    /// keccak256(pool || bytes32(epoch)), where the pool is this contract's address.
    function sourceId(uint64 epoch) public view returns (bytes32) {
        return keccak256(abi.encodePacked(address(this), bytes32(uint256(epoch))));
    }

    /// @notice The nullifier domain of an epoch of this pool on this chain.
    /// @param epoch The epoch of the root a spend proves against.
    function domain(uint64 epoch) public view returns (bytes32) {
        return domainFor(block.chainid, address(this), epoch);
    }

    /// @notice keccak256(DOMAIN_TAG || chainId || pool || epoch) mod p, over 32-byte words.
    /// The domain keeps nullifiers of different chains, pools and epochs apart. Leaf
    /// indices restart with each epoch, so without the epoch, equal commitments at the same
    /// index of two epochs would share a nullifier.
    /// @param epoch The epoch of the root a spend proves against.
    function domainFor(uint256 chainId, address pool, uint64 epoch) public pure returns (bytes32) {
        return bytes32(
            uint256(keccak256(abi.encodePacked(DOMAIN_TAG, chainId, bytes32(uint256(uint160(pool))), uint256(epoch))))
                % P
        );
    }

    /// @notice Deposits msg.value as a note: appends Poseidon(2, inner, msg.value) to the
    /// current tree and emits the note. Anyone may call it.
    /// @dev The commitment takes its value from msg.value, so a note never holds more than
    /// was paid in. A full tree starts a new epoch first.
    /// @param inner The recipient's Poseidon(owner_pk, rho), below p.
    /// @param note One note, optionally after an ML-KEM-768 ciphertext. Only its length is
    /// checked.
    /// @return index The new leaf's index in the current epoch's tree.
    function shield(bytes32 inner, bytes calldata note) external payable onlyDelegate returns (uint32 index) {
        if (msg.value == 0) revert ZeroValueShield();
        if (msg.value >= MAX_VALUE) revert ValueTooLarge();
        if (uint256(inner) >= P) revert NotCanonical();
        if (note.length != NOTE_BYTES && note.length != KEM_CIPHERTEXT_BYTES + NOTE_BYTES) revert InvalidNotes();

        bytes32 cm = bytes32(_hash3(2, uint256(inner), msg.value));
        if (cm == SINK_0 || cm == SINK_1) revert ReservedSink();

        _ensureCapacity(1);
        index = _insert(cm);
        currentRoot = _computeRoot();
        emit LeafAppended(cm, currentEpoch, index, currentRoot);
        emit Notes(note);
    }

    /// @notice Settles a spend the dispatcher has approved: appends its outputs other than
    /// sinks, credits any withdrawal to its recipient and emits its notes. Only the pool
    /// itself can call it, as the SENDER frame of the spend's frame transaction.
    /// @dev Approval has already consumed the nullifiers, so a refusal here would burn the
    /// notes. Every check below was made before approval: the dispatcher checks the notes'
    /// length, the nullifiers, authorizer, domain, field elements, amounts and recipient; the
    /// proof makes the outputs distinct and each sink sit in its own position; and the
    /// recent-root frame proves a root the pool published for the epoch, which
    /// publishEpochRoot does only for an epoch up to currentEpoch. The calldata is
    /// settle(Spend) followed by two notes, optionally after an ML-KEM-768 ciphertext, and
    /// the authorizer's signature covers them.
    function settle(Spend calldata s) external onlyDelegate {
        if (msg.sender != address(this)) revert NotPoolSender();
        // The dispatcher admits the same two lengths before approval.
        uint256 notesLength = msg.data.length - SETTLE_SPEND_BYTES;
        if (notesLength != 2 * NOTE_BYTES && notesLength != KEM_CIPHERTEXT_BYTES + 2 * NOTE_BYTES) {
            revert InvalidNotes();
        }
        if (s.nf1 == bytes32(0) || s.nf2 == bytes32(0)) revert ZeroNullifier();
        if (s.authorizer == address(0)) revert InvalidAuthorizer();
        if (s.domain != domain(s.epoch)) revert InvalidDomain();
        if (s.epoch > currentEpoch) revert InvalidEpoch();
        if (
            uint256(s.root) >= P || uint256(s.domain) >= P || uint256(s.nf1) >= P || uint256(s.nf2) >= P
                || uint256(s.outCm1) >= P || uint256(s.outCm2) >= P
        ) revert NotCanonical();
        if (s.publicAmount >= MAX_VALUE || s.fee >= MAX_VALUE) revert ValueTooLarge();
        if ((s.publicAmount == 0) != (s.recipient == address(0))) revert InvalidSettlementShape();
        if (s.outCm1 == s.outCm2 || s.outCm1 == SINK_1 || s.outCm2 == SINK_0) {
            revert InvalidSettlementShape();
        }
        // Each output other than a sink becomes a new leaf, even when the tree already
        // holds the same commitment: nullifiers bind the leaf's epoch and index, so the two
        // leaves are separate notes.

        emit NoteSpent(s.nf1);
        emit NoteSpent(s.nf2);

        uint32 appendCount;
        if (s.outCm1 != SINK_0) appendCount++;
        if (s.outCm2 != SINK_1) appendCount++;
        _ensureCapacity(appendCount);

        bool new1 = s.outCm1 != SINK_0;
        bool new2 = s.outCm2 != SINK_1;
        uint32 i1;
        uint32 i2;
        if (new1) i1 = _insert(s.outCm1);
        if (new2) i2 = _insert(s.outCm2);
        if (new1 || new2) {
            currentRoot = _computeRoot();
            if (new1) emit LeafAppended(s.outCm1, currentEpoch, i1, currentRoot);
            if (new2) emit LeafAppended(s.outCm2, currentEpoch, i2, currentRoot);
        }

        if (s.publicAmount != 0) {
            withdrawalCredit[s.recipient] += s.publicAmount;
            emit WithdrawalCredited(s.recipient, s.publicAmount);
        }
        emit Notes(msg.data[SETTLE_SPEND_BYTES:]);
    }

    /// @notice Writes an epoch's root to EIP-8272, so spends can prove against it. Anyone
    /// may call it: the root comes from pool state, never from the caller.
    /// @dev Settlement never publishes, so a failed publication cannot consume approved
    /// note keys without creating the promised outputs. EIP-8272 keeps only the last root
    /// a source writes in a slot, so a second publication of an epoch in one slot replaces
    /// the first.
    /// @param epoch The current epoch, whose root changes as leaves arrive, or a closed one.
    function publishEpochRoot(uint64 epoch) external onlyDelegate {
        bytes32 root;
        if (epoch == currentEpoch) root = currentRoot;
        else if (epoch < currentEpoch) root = finalRoot[epoch];
        else revert InvalidEpoch();
        if (root == bytes32(0)) revert InvalidRoot();

        bytes32 salt = bytes32(uint256(epoch));
        (bool ok,) = RECENT_ROOT_PREDEPLOY.call(abi.encodePacked(salt, root));
        if (!ok) revert RootPublishFailed();
        emit RootPublished(epoch, sourceId(epoch), root);
    }

    /// @notice Pays a recipient its whole withdrawal credit with a plain ETH call. Anyone
    /// may call it, and the ETH goes only to who.
    /// @dev The credit is zeroed before the call, so a recipient that reenters is paid once.
    /// A failed payout reverts the claim and keeps the credit for a later one.
    function claimWithdrawal(address payable who) external onlyDelegate {
        uint256 amount = withdrawalCredit[who];
        if (amount == 0) revert NoCredit();
        withdrawalCredit[who] = 0;
        emit Withdrawn(who, amount);
        (bool ok,) = who.call{value: amount}("");
        if (!ok) revert PayoutFailed();
    }

    /// @dev Starts a new epoch when the current tree lacks room for count leaves, so an
    /// insertion never fails for lack of room after approval.
    function _ensureCapacity(uint32 count) internal {
        if (count > CAPACITY - nextIndex) _rollEpoch();
    }

    function _rollEpoch() internal {
        uint64 closed = currentEpoch;
        bytes32 closedRoot = currentRoot;
        finalRoot[closed] = closedRoot;
        currentEpoch = closed + 1;
        nextIndex = 0;
        currentRoot = EMPTY_ROOT;
        for (uint32 l = 0; l <= DEPTH; l++) {
            delete filledSubtrees[l];
        }
        emit EpochRolled(closed, closedRoot, currentEpoch);
    }

    function _hashPair(bytes32 l, bytes32 r) internal view returns (bytes32) {
        return bytes32(_hash2(uint256(l), uint256(r)));
    }

    /// @dev Poseidon(x0, x1) from PoseidonT3.hash2 (selector 0x511c53ff). A failed call, a
    /// return other than one word, or an output of p or more reverts, so a faulty library
    /// cannot put a non-canonical node in the tree.
    function _hash2(uint256 x0, uint256 x1) internal view returns (uint256 out) {
        (bool ok, bytes memory ret) =
            POSEIDON_T3.staticcall{gas: 200_000}(abi.encodeWithSelector(bytes4(0x511c53ff), x0, x1));
        if (!ok || ret.length != 32) revert HashFailed();
        out = abi.decode(ret, (uint256));
        if (out >= P) revert HashFailed();
    }

    /// @dev Poseidon(x0, x1, x2) from PoseidonT4.hash3 (selector 0x2dbf86c6), checked as in
    /// _hash2.
    function _hash3(uint256 x0, uint256 x1, uint256 x2) internal view returns (uint256 out) {
        (bool ok, bytes memory ret) =
            POSEIDON_T4.staticcall{gas: 200_000}(abi.encodeWithSelector(bytes4(0x2dbf86c6), x0, x1, x2));
        if (!ok || ret.length != 32) revert HashFailed();
        out = abi.decode(ret, (uint256));
        if (out >= P) revert HashFailed();
    }

    /// @dev Appends cm at nextIndex. filledSubtrees[l] holds the root of the last complete
    /// left subtree of height l: while the new node is a right child, it is hashed with
    /// that subtree and carried up, and it is stored at the first height where it is a left
    /// child. The last leaf of a full tree carries all the way to filledSubtrees[DEPTH].
    function _insert(bytes32 cm) internal returns (uint32 index) {
        index = nextIndex;
        nextIndex = index + 1;
        bytes32 node = cm;
        uint32 idx = index;
        uint32 l;
        while (idx & 1 == 1) {
            node = _hashPair(filledSubtrees[l], node);
            idx >>= 1;
            l++;
        }
        filledSubtrees[l] = node;
    }

    /// @dev The current tree's root, with empty subtrees to the right of the last leaf. A
    /// full tree's root is filledSubtrees[DEPTH].
    function _computeRoot() internal view returns (bytes32 node) {
        uint32 idx = nextIndex;
        if (idx == CAPACITY) return filledSubtrees[DEPTH];
        for (uint32 l = 0; l < DEPTH; l++) {
            node = idx & 1 == 0 ? _hashPair(node, _zeros(l)) : _hashPair(filledSubtrees[l], node);
            idx >>= 1;
        }
    }

    /// @dev The root of an empty subtree of height l: zeros(0) = 0 and zeros(l) =
    /// Poseidon(zeros(l - 1), zeros(l - 1)), so zeros(DEPTH) is EMPTY_ROOT.
    function _zeros(uint32 l) internal pure returns (bytes32) {
        if (l == 0) return bytes32(0);
        if (l == 1) return 0x2098f5fb9e239eab3ceac3f27b81e481dc3124d55ffed523a839ee8446b64864;
        if (l == 2) return 0x1069673dcdb12263df301a6ff584a7ec261a44cb9dc68df067a4774460b1f1e1;
        if (l == 3) return 0x18f43331537ee2af2e3d758d50f72106467c6eea50371dd528d57eb2b856d238;
        if (l == 4) return 0x07f9d837cb17b0d36320ffe93ba52345f1b728571a568265caac97559dbc952a;
        if (l == 5) return 0x2b94cf5e8746b3f5c9631f4c5df32907a699c58c94b2ad4d7b5cec1639183f55;
        if (l == 6) return 0x2dee93c5a666459646ea7d22cca9e1bcfed71e6951b953611d11dda32ea09d78;
        if (l == 7) return 0x078295e5a22b84e982cf601eb639597b8b0515a88cb5ac7fa8a4aabe3c87349d;
        if (l == 8) return 0x2fa5e5f18f6027a6501bec864564472a616b2e274a41211a444cbe3a99f3cc61;
        if (l == 9) return 0x0e884376d0d8fd21ecb780389e941f66e45e7acce3e228ab3e2156a614fcd747;
        if (l == 10) return 0x1b7201da72494f1e28717ad1a52eb469f95892f957713533de6175e5da190af2;
        if (l == 11) return 0x1f8d8822725e36385200c0b201249819a6e6e1e4650808b5bebc6bface7d7636;
        if (l == 12) return 0x2c5d82f66c914bafb9701589ba8cfcfb6162b0a12acf88a8d0879a0471b5f85a;
        if (l == 13) return 0x14c54148a0940bb820957f5adf3fa1134ef5c4aaa113f4646458f270e0bfbfd0;
        if (l == 14) return 0x190d33b12f986f961e10c0ee44d8b9af11be25588cad89d416118e4bf4ebe80c;
        if (l == 15) return 0x22f98aa9ce704152ac17354914ad73ed1167ae6596af510aa5b3649325e06c92;
        if (l == 16) return 0x2a7c7c9b6ce5880b9f6f228d72bf6a575a526f29c66ecceef8b753d38bba7323;
        if (l == 17) return 0x2e8186e558698ec1c67af9c14d463ffc470043c9c2988b954d75dd643f36b992;
        if (l == 18) return 0x0f57c5571e9a4eab49e2c8cf050dae948aef6ead647392273546249d1c1ff10f;
        if (l == 19) return 0x1830ee67b5fb554ad5f63d4388800e1cfe78e310697d46e43c9ce36134f72cca;
        return EMPTY_ROOT;
    }
}
