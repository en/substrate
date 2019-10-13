// Copyright 2017-2019 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

use primitives::{
	blake2_128, blake2_256, twox_128, twox_256, twox_64, ed25519, Blake2Hasher, sr25519, Pair, H256,
	traits::Externalities, child_storage_key::ChildStorageKey, hexdisplay::HexDisplay, offchain,
	Hasher,
};
// Switch to this after PoC-3
// pub use primitives::BlakeHasher;
pub use substrate_state_machine::{BasicExternalities, TestExternalities};

use environmental::environmental;
use trie::{TrieConfiguration, trie_types::Layout};

use std::{collections::HashMap, convert::TryFrom};

environmental!(ext: trait Externalities<Blake2Hasher>);

use std::cell::RefCell;

use wasmi::{
    memory_units, Error, Externals, FuncInstance, FuncRef, MemoryDescriptor, MemoryInstance,
    MemoryRef, ModuleImportResolver, RuntimeArgs, RuntimeValue, Signature, Trap, ValueType,
};

use wasmi::{
     ImportsBuilder, Module, ModuleInstance, ModuleRef, LINEAR_MEMORY_PAGE_SIZE,
};

fn create_default_host_externals() -> HostExternals {
    HostExternals::new(
        (MAX_RUNTIME_MEM / LINEAR_MEMORY_PAGE_SIZE.0) as u32,
        RefCell::new(None),
    )
}

/// create wasm instance
pub fn create_wasm_instance<B: AsRef<[u8]>>(wasm_bin: B) -> Result<ModuleRef, Error> {
    let module = Module::from_buffer(wasm_bin)?;
    let module_resolver = create_default_host_externals();
    let imports = ImportsBuilder::new().with_resolver("env", &module_resolver);
    let instance = ModuleInstance::new(&module, &imports)?.assert_no_start();
    Ok(instance)
}


/// pass wasm instance and invoke export function by name and args
pub fn invoke_export(
    instance: &ModuleRef,
    func_name: &str,
    args: &[RuntimeValue],
) -> Result<Option<RuntimeValue>, Error> {
    let mut host  = create_default_host_externals();
    instance.invoke_export(func_name, args, &mut host)
}

mod env {
    use super::*;

    pub const ADD_FUNC_INDEX: usize = 0;
    pub const CHECK_READ_PROOF: usize = 1;

    pub fn check_read_proof() -> Result<Option<RuntimeValue>, Trap> {
        Ok(Some(RuntimeValue::I32(0)))
    }

    pub fn add(args: RuntimeArgs) -> Result<Option<RuntimeValue>, Trap> {
        let a: u32 = args.nth_checked(0)?;
        let b: u32 = args.nth_checked(1)?;
        let result = a + b;
        Ok(Some(RuntimeValue::I32(result as i32)))
    }
}

// maximum memory in bytes
pub const MAX_RUNTIME_MEM: usize = 1024 * 1024 * 1024; // 1 GiB
pub const MAX_CODE_MEM: usize = 16 * 1024 * 1024; // 16 MiB

/// HostExternals for index host functions and resolve importer
#[derive(Debug, Default)]
pub struct HostExternals {
    max_memory: u32, // in pages.
    memory: RefCell<Option<MemoryRef>>,
}

impl HostExternals {
    /// Create a host external interface
    pub fn new(max_memory: u32, memory: RefCell<Option<MemoryRef>>) -> Self {
        Self { max_memory, memory }
    }

    fn check_signature(&self, index: usize, signature: &Signature) -> bool {
        let (params, ret_ty): (&[ValueType], Option<ValueType>) = match index {
            env::ADD_FUNC_INDEX => (&[ValueType::I32, ValueType::I32], Some(ValueType::I32)),
            env::CHECK_READ_PROOF => (&[], Some(ValueType::I32)),

            _ => return false,
        };
        signature.params() == params && signature.return_type() == ret_ty
    }
}

// for index functions
impl Externals for HostExternals {
    fn invoke_index(
        &mut self,
        index: usize,
        args: RuntimeArgs,
    ) -> Result<Option<RuntimeValue>, Trap> {
        match index {
            env::ADD_FUNC_INDEX => env::add(args),

            env::CHECK_READ_PROOF => env::check_read_proof(),

            _ => panic!("Unimplemented function at {}", index),
        }
    }
}

// resolve name to host functions
impl ModuleImportResolver for HostExternals {
    fn resolve_func(&self, field_name: &str, signature: &Signature) -> Result<FuncRef, Error> {
        match field_name {
            "ext_add" => {
                let (params, ret_ty) =
                    (&[ValueType::I32, ValueType::I32][..], Some(ValueType::I32));
                if signature.params() != params || signature.return_type() != ret_ty {
                    Err(Error::Instantiation(format!(
                        "Export {} has a bad signature",
                        field_name
                    )))
                } else {
                    Ok(FuncInstance::alloc_host(
                        Signature::new(params, ret_ty),
                        env::ADD_FUNC_INDEX,
                    ))
                }
            }
            "ext_check_read_proof" => {
                let (params, ret_ty) = (&[][..], Some(ValueType::I32));
                if signature.params() != params || signature.return_type() != ret_ty {
                    Err(Error::Instantiation(format!(
                        "Export {} has a bad signature",
                        field_name
                    )))
                } else {
                    Ok(FuncInstance::alloc_host(
                        Signature::new(params, ret_ty),
                        env::ADD_FUNC_INDEX,
                    ))
                }
            }

            _ => {
                return Err(Error::Instantiation(format!(
                    "Export {} not found",
                    field_name
                )));
            }
        }
    }

    fn resolve_memory(
        &self,
        field_name: &str,
        descriptor: &MemoryDescriptor,
    ) -> Result<MemoryRef, Error> {
        if field_name == "memory" {
            let effective_max = descriptor.maximum().unwrap_or(self.max_memory);
            if descriptor.initial() > self.max_memory || effective_max > self.max_memory {
                Err(Error::Instantiation(
                    "Module requested too much memory".to_owned(),
                ))
            } else {
                let mem = MemoryInstance::alloc(
                    memory_units::Pages(descriptor.initial() as usize),
                    descriptor
                        .maximum()
                        .map(|x| memory_units::Pages(x as usize)),
                )?;
                *self.memory.borrow_mut() = Some(mem.clone());
                Ok(mem)
            }
        } else {
            Err(Error::Instantiation(
                "Memory imported under unknown name".to_owned(),
            ))
        }
    }
}

/// Additional bounds for `Hasher` trait for with_std.
pub trait HasherBounds {}
impl<T: Hasher> HasherBounds for T {}

/// Returns a `ChildStorageKey` if the given `storage_key` slice is a valid storage
/// key or panics otherwise.
///
/// Panicking here is aligned with what the `without_std` environment would do
/// in the case of an invalid child storage key.
fn child_storage_key_or_panic(storage_key: &[u8]) -> ChildStorageKey {
	match ChildStorageKey::from_slice(storage_key) {
		Some(storage_key) => storage_key,
		None => panic!("child storage key is invalid"),
	}
}

impl StorageApi for () {
	fn storage(key: &[u8]) -> Option<Vec<u8>> {
		ext::with(|ext| ext.storage(key).map(|s| s.to_vec()))
			.expect("storage cannot be called outside of an Externalities-provided environment.")
	}

	fn read_storage(key: &[u8], value_out: &mut [u8], value_offset: usize) -> Option<usize> {
		ext::with(|ext| ext.storage(key).map(|value| {
			let data = &value[value_offset.min(value.len())..];
			let written = std::cmp::min(data.len(), value_out.len());
			value_out[..written].copy_from_slice(&data[..written]);
			value.len()
		})).expect("read_storage cannot be called outside of an Externalities-provided environment.")
	}

	fn child_storage(storage_key: &[u8], key: &[u8]) -> Option<Vec<u8>> {
		ext::with(|ext| {
			let storage_key = child_storage_key_or_panic(storage_key);
			ext.child_storage(storage_key, key).map(|s| s.to_vec())
		})
		.expect("storage cannot be called outside of an Externalities-provided environment.")
	}

	fn set_storage(key: &[u8], value: &[u8]) {
		ext::with(|ext|
			ext.set_storage(key.to_vec(), value.to_vec())
		);
	}

	fn read_child_storage(
		storage_key: &[u8],
		key: &[u8],
		value_out: &mut [u8],
		value_offset: usize,
	) -> Option<usize> {
		ext::with(|ext| {
			let storage_key = child_storage_key_or_panic(storage_key);
			ext.child_storage(storage_key, key)
				.map(|value| {
					let data = &value[value_offset.min(value.len())..];
					let written = std::cmp::min(data.len(), value_out.len());
					value_out[..written].copy_from_slice(&data[..written]);
					value.len()
				})
		})
		.expect("read_child_storage cannot be called outside of an Externalities-provided environment.")
	}

	fn set_child_storage(storage_key: &[u8], key: &[u8], value: &[u8]) {
		ext::with(|ext| {
			let storage_key = child_storage_key_or_panic(storage_key);
			ext.set_child_storage(storage_key, key.to_vec(), value.to_vec())
		});
	}

	fn clear_storage(key: &[u8]) {
		ext::with(|ext|
			ext.clear_storage(key)
		);
	}

	fn clear_child_storage(storage_key: &[u8], key: &[u8]) {
		ext::with(|ext| {
			let storage_key = child_storage_key_or_panic(storage_key);
			ext.clear_child_storage(storage_key, key)
		});
	}

	fn kill_child_storage(storage_key: &[u8]) {
		ext::with(|ext| {
			let storage_key = child_storage_key_or_panic(storage_key);
			ext.kill_child_storage(storage_key)
		});
	}

	fn exists_storage(key: &[u8]) -> bool {
		ext::with(|ext|
			ext.exists_storage(key)
		).unwrap_or(false)
	}

	fn exists_child_storage(storage_key: &[u8], key: &[u8]) -> bool {
		ext::with(|ext| {
			let storage_key = child_storage_key_or_panic(storage_key);
			ext.exists_child_storage(storage_key, key)
		}).unwrap_or(false)
	}

	fn clear_prefix(prefix: &[u8]) {
		ext::with(|ext|
			ext.clear_prefix(prefix)
		);
	}

	fn clear_child_prefix(storage_key: &[u8], prefix: &[u8]) {
		ext::with(|ext| {
			let storage_key = child_storage_key_or_panic(storage_key);
			ext.clear_child_prefix(storage_key, prefix)
		});
	}

	fn storage_root() -> [u8; 32] {
		ext::with(|ext|
			ext.storage_root()
		).unwrap_or(H256::zero()).into()
	}

	fn child_storage_root(storage_key: &[u8]) -> Vec<u8> {
		ext::with(|ext| {
			let storage_key = child_storage_key_or_panic(storage_key);
			ext.child_storage_root(storage_key)
		}).expect("child_storage_root cannot be called outside of an Externalities-provided environment.")
	}

	fn storage_changes_root(parent_hash: [u8; 32]) -> Option<[u8; 32]> {
		ext::with(|ext|
			ext.storage_changes_root(parent_hash.into()).map(|h| h.map(|h| h.into()))
		).unwrap_or(Ok(None)).expect("Invalid parent hash passed to storage_changes_root")
	}

	fn blake2_256_trie_root(input: Vec<(Vec<u8>, Vec<u8>)>) -> H256 {
		Layout::<Blake2Hasher>::trie_root(input)
	}

	fn blake2_256_ordered_trie_root(input: Vec<Vec<u8>>) -> H256 {
		Layout::<Blake2Hasher>::ordered_trie_root(input)
	}
}

impl OtherApi for () {
	fn chain_id() -> u64 {
		ext::with(|ext|
			ext.chain_id()
		).unwrap_or(0)
	}

	fn run_wasm() {
		use std::fs;

		let wasm = fs::read("/tmp/proof.compact.wasm").expect("file not found");
		let instance = create_wasm_instance(wasm).expect("create wasm error!!!!!!");
		let args = [];
		let res = invoke_export(&instance, "check_read_proof", &args).expect("has no err").expect("has return value");
		println!("result: {:?}", res);
	}

	fn print_num(val: u64) {
		println!("{}", val);
	}

	fn print_utf8(utf8: &[u8]) {
		if let Ok(data) = std::str::from_utf8(utf8) {
			println!("{}", data)
		}
	}

	fn print_hex(data: &[u8]) {
		println!("{}", HexDisplay::from(&data));
	}
}

impl CryptoApi for () {
	fn ed25519_public_keys(id: KeyTypeId) -> Vec<ed25519::Public> {
		ext::with(|ext| {
			ext.keystore()
				.expect("No `keystore` associated for the current context!")
				.read()
				.ed25519_public_keys(id)
		}).expect("`ed25519_public_keys` cannot be called outside of an Externalities-provided environment.")
	}

	fn ed25519_generate(id: KeyTypeId, seed: Option<&str>) -> ed25519::Public {
		ext::with(|ext| {
			ext.keystore()
				.expect("No `keystore` associated for the current context!")
				.write()
				.ed25519_generate_new(id, seed)
				.expect("`ed25519_generate` failed")
		}).expect("`ed25519_generate` cannot be called outside of an Externalities-provided environment.")
	}

	fn ed25519_sign(
		id: KeyTypeId,
		pubkey: &ed25519::Public,
		msg: &[u8],
	) -> Option<ed25519::Signature> {
		let pub_key = ed25519::Public::try_from(pubkey.as_ref()).ok()?;

		ext::with(|ext| {
			ext.keystore()
				.expect("No `keystore` associated for the current context!")
				.read()
				.ed25519_key_pair(id, &pub_key)
				.map(|k| k.sign(msg))
		}).expect("`ed25519_sign` cannot be called outside of an Externalities-provided environment.")
	}

	fn ed25519_verify(sig: &ed25519::Signature, msg: &[u8], pubkey: &ed25519::Public) -> bool {
		ed25519::Pair::verify(sig, msg, pubkey)
	}

	fn sr25519_public_keys(id: KeyTypeId) -> Vec<sr25519::Public> {
		ext::with(|ext| {
			ext.keystore()
				.expect("No `keystore` associated for the current context!")
				.read()
				.sr25519_public_keys(id)
		}).expect("`sr25519_public_keys` cannot be called outside of an Externalities-provided environment.")
	}

	fn sr25519_generate(id: KeyTypeId, seed: Option<&str>) -> sr25519::Public {
		ext::with(|ext| {
			ext.keystore()
				.expect("No `keystore` associated for the current context!")
				.write()
				.sr25519_generate_new(id, seed)
				.expect("`sr25519_generate` failed")
		}).expect("`sr25519_generate` cannot be called outside of an Externalities-provided environment.")
	}

	fn sr25519_sign(
		id: KeyTypeId,
		pubkey: &sr25519::Public,
		msg: &[u8],
	) -> Option<sr25519::Signature> {
		let pub_key = sr25519::Public::try_from(pubkey.as_ref()).ok()?;

		ext::with(|ext| {
			ext.keystore()
				.expect("No `keystore` associated for the current context!")
				.read()
				.sr25519_key_pair(id, &pub_key)
				.map(|k| k.sign(msg))
		}).expect("`sr25519_sign` cannot be called outside of an Externalities-provided environment.")
	}

	fn sr25519_verify(sig: &sr25519::Signature, msg: &[u8], pubkey: &sr25519::Public) -> bool {
		sr25519::Pair::verify(sig, msg, pubkey)
	}

	fn secp256k1_ecdsa_recover(sig: &[u8; 65], msg: &[u8; 32]) -> Result<[u8; 64], EcdsaVerifyError> {
		let rs = secp256k1::Signature::parse_slice(&sig[0..64])
			.map_err(|_| EcdsaVerifyError::BadRS)?;
		let v = secp256k1::RecoveryId::parse(if sig[64] > 26 { sig[64] - 27 } else { sig[64] } as u8)
			.map_err(|_| EcdsaVerifyError::BadV)?;
		let pubkey = secp256k1::recover(&secp256k1::Message::parse(msg), &rs, &v)
			.map_err(|_| EcdsaVerifyError::BadSignature)?;
		let mut res = [0u8; 64];
		res.copy_from_slice(&pubkey.serialize()[1..65]);
		Ok(res)
	}
}

impl HashingApi for () {
	fn keccak_256(data: &[u8]) -> [u8; 32] {
		tiny_keccak::keccak256(data)
	}

	fn blake2_128(data: &[u8]) -> [u8; 16] {
		blake2_128(data)
	}

	fn blake2_256(data: &[u8]) -> [u8; 32] {
		blake2_256(data)
	}

	fn twox_256(data: &[u8]) -> [u8; 32] {
		twox_256(data)
	}

	fn twox_128(data: &[u8]) -> [u8; 16] {
		twox_128(data)
	}

	fn twox_64(data: &[u8]) -> [u8; 8] {
		twox_64(data)
	}
}

fn with_offchain<R>(f: impl FnOnce(&mut dyn offchain::Externalities) -> R, msg: &'static str) -> R {
	ext::with(|ext| ext
		.offchain()
		.map(|ext| f(ext))
		.expect(msg)
	).expect("offchain-worker functions cannot be called outside of an Externalities-provided environment.")
}

impl OffchainApi for () {
	fn is_validator() -> bool {
		with_offchain(|ext| {
			ext.is_validator()
		}, "is_validator can be called only in the offchain worker context")
	}

	fn submit_transaction(data: Vec<u8>) -> Result<(), ()> {
		with_offchain(|ext| {
			ext.submit_transaction(data)
		}, "submit_transaction can be called only in the offchain worker context")
	}

	fn network_state() -> Result<OpaqueNetworkState, ()> {
		with_offchain(|ext| {
			ext.network_state()
		}, "network_state can be called only in the offchain worker context")
	}

	fn timestamp() -> offchain::Timestamp {
		with_offchain(|ext| {
			ext.timestamp()
		}, "timestamp can be called only in the offchain worker context")
	}

	fn sleep_until(deadline: offchain::Timestamp) {
		with_offchain(|ext| {
			ext.sleep_until(deadline)
		}, "sleep_until can be called only in the offchain worker context")
	}

	fn random_seed() -> [u8; 32] {
		with_offchain(|ext| {
			ext.random_seed()
		}, "random_seed can be called only in the offchain worker context")
	}

	fn local_storage_set(kind: offchain::StorageKind, key: &[u8], value: &[u8]) {
		with_offchain(|ext| {
			ext.local_storage_set(kind, key, value)
		}, "local_storage_set can be called only in the offchain worker context")
	}

	fn local_storage_compare_and_set(
		kind: offchain::StorageKind,
		key: &[u8],
		old_value: Option<&[u8]>,
		new_value: &[u8],
	) -> bool {
		with_offchain(|ext| {
			ext.local_storage_compare_and_set(kind, key, old_value, new_value)
		}, "local_storage_compare_and_set can be called only in the offchain worker context")
	}

	fn local_storage_get(kind: offchain::StorageKind, key: &[u8]) -> Option<Vec<u8>> {
		with_offchain(|ext| {
			ext.local_storage_get(kind, key)
		}, "local_storage_get can be called only in the offchain worker context")
	}

	fn http_request_start(
		method: &str,
		uri: &str,
		meta: &[u8],
	) -> Result<offchain::HttpRequestId, ()> {
		with_offchain(|ext| {
			ext.http_request_start(method, uri, meta)
		}, "http_request_start can be called only in the offchain worker context")
	}

	fn http_request_add_header(
		request_id: offchain::HttpRequestId,
		name: &str,
		value: &str,
	) -> Result<(), ()> {
		with_offchain(|ext| {
			ext.http_request_add_header(request_id, name, value)
		}, "http_request_add_header can be called only in the offchain worker context")
	}

	fn http_request_write_body(
		request_id: offchain::HttpRequestId,
		chunk: &[u8],
		deadline: Option<offchain::Timestamp>,
	) -> Result<(), offchain::HttpError> {
		with_offchain(|ext| {
			ext.http_request_write_body(request_id, chunk, deadline)
		}, "http_request_write_body can be called only in the offchain worker context")
	}

	fn http_response_wait(
		ids: &[offchain::HttpRequestId],
		deadline: Option<offchain::Timestamp>,
	) -> Vec<offchain::HttpRequestStatus> {
		with_offchain(|ext| {
			ext.http_response_wait(ids, deadline)
		}, "http_response_wait can be called only in the offchain worker context")
	}

	fn http_response_headers(
		request_id: offchain::HttpRequestId,
	) -> Vec<(Vec<u8>, Vec<u8>)> {
		with_offchain(|ext| {
			ext.http_response_headers(request_id)
		}, "http_response_headers can be called only in the offchain worker context")
	}

	fn http_response_read_body(
		request_id: offchain::HttpRequestId,
		buffer: &mut [u8],
		deadline: Option<offchain::Timestamp>,
	) -> Result<usize, offchain::HttpError> {
		with_offchain(|ext| {
			ext.http_response_read_body(request_id, buffer, deadline)
		}, "http_response_read_body can be called only in the offchain worker context")
	}
}

impl Api for () {}

/// Execute the given closure with global function available whose functionality routes into the
/// externalities `ext`. Forwards the value that the closure returns.
// NOTE: need a concrete hasher here due to limitations of the `environmental!` macro, otherwise a type param would have been fine I think.
pub fn with_externalities<R, F: FnOnce() -> R>(ext: &mut dyn Externalities<Blake2Hasher>, f: F) -> R {
	ext::using(ext, f)
}

/// A set of key value pairs for storage.
pub type StorageOverlay = HashMap<Vec<u8>, Vec<u8>>;

/// A set of key value pairs for children storage;
pub type ChildrenStorageOverlay = HashMap<Vec<u8>, StorageOverlay>;

/// Execute the given closure with global functions available whose functionality routes into
/// externalities that draw from and populate `storage` and `children_storage`.
/// Forwards the value that the closure returns.
pub fn with_storage<R, F: FnOnce() -> R>(
	storage: &mut (StorageOverlay, ChildrenStorageOverlay),
	f: F
) -> R {
	let mut alt_storage = Default::default();
	rstd::mem::swap(&mut alt_storage, storage);

	let mut ext = BasicExternalities::new(alt_storage.0, alt_storage.1);
	let r = ext::using(&mut ext, f);

	*storage = ext.into_storages();

	r
}

#[cfg(test)]
mod std_tests {
	use super::*;
	use primitives::map;

	#[test]
	fn storage_works() {
		let mut t = BasicExternalities::default();
		assert!(with_externalities(&mut t, || {
			assert_eq!(storage(b"hello"), None);
			set_storage(b"hello", b"world");
			assert_eq!(storage(b"hello"), Some(b"world".to_vec()));
			assert_eq!(storage(b"foo"), None);
			set_storage(b"foo", &[1, 2, 3][..]);
			true
		}));

		t = BasicExternalities::new(map![b"foo".to_vec() => b"bar".to_vec()], map![]);

		assert!(!with_externalities(&mut t, || {
			assert_eq!(storage(b"hello"), None);
			assert_eq!(storage(b"foo"), Some(b"bar".to_vec()));
			false
		}));
	}

	#[test]
	fn read_storage_works() {
		let mut t = BasicExternalities::new(map![
			b":test".to_vec() => b"\x0b\0\0\0Hello world".to_vec()
		], map![]);

		with_externalities(&mut t, || {
			let mut v = [0u8; 4];
			assert!(read_storage(b":test", &mut v[..], 0).unwrap() >= 4);
			assert_eq!(v, [11u8, 0, 0, 0]);
			let mut w = [0u8; 11];
			assert!(read_storage(b":test", &mut w[..], 4).unwrap() >= 11);
			assert_eq!(&w, b"Hello world");
		});
	}

	#[test]
	fn clear_prefix_works() {
		let mut t = BasicExternalities::new(map![
			b":a".to_vec() => b"\x0b\0\0\0Hello world".to_vec(),
			b":abcd".to_vec() => b"\x0b\0\0\0Hello world".to_vec(),
			b":abc".to_vec() => b"\x0b\0\0\0Hello world".to_vec(),
			b":abdd".to_vec() => b"\x0b\0\0\0Hello world".to_vec()
		], map![]);

		with_externalities(&mut t, || {
			clear_prefix(b":abc");

			assert!(storage(b":a").is_some());
			assert!(storage(b":abdd").is_some());
			assert!(storage(b":abcd").is_none());
			assert!(storage(b":abc").is_none());
		});
	}
}
