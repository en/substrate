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
use hash_db::Hasher;
use primitives::H256;
use sr_primitives::traits::{Block as BlockT, Header as HeaderT, BlakeTwo256};
use sr_primitives::generic;
use substrate_state_machine::read_proof_check;
use primitives::Blake2Hasher;

use std::collections::HashMap;
use std::marker::PhantomData;
use core::mem::transmute;

use sandbox::{EnvironmentDefinitionBuilder, HostError, Instance, ReturnValue, TypedValue};

#[derive(Debug)]
pub enum ProofError {
	Proof,
}

/// Hash conversion. Used to convert between unbound associated hash types in traits,
/// implemented by the same hash type.
/// Panics if used to convert between different hash types.
fn convert_hash<H1: Default + AsMut<[u8]>, H2: AsRef<[u8]>>(src: &H2) -> H1 {
	let mut dest = H1::default();
	assert_eq!(dest.as_mut().len(), src.as_ref().len());
	dest.as_mut().copy_from_slice(src.as_ref());
	dest
}

pub fn check_read_proof_<Block: BlockT, H: Hasher<Out = H256>>(
	request: &RemoteReadRequest<Block::Header>,
	remote_proof: Vec<Vec<u8>>,
) -> Result<HashMap<Vec<u8>, Option<Vec<u8>>>, ProofError> {
	let _hasher: PhantomData<(Block, H)> = PhantomData;
	read_proof_check::<H, _>(
		convert_hash(request.header.state_root()),
		remote_proof,
		request.keys.iter(),
	)
		.map_err(|_e| ProofError::Proof)
}


fn execute_wasm(code: &[u8], args: &[TypedValue]) -> Result<ReturnValue, HostError> {
	struct State {
		counter: u32,
	}

	fn check_read_proof(_e: &mut State, args: &[TypedValue]) -> Result<ReturnValue, HostError> {
		if args.len() != 2 {
			return Err(HostError);
		}
		let arg1 = match args[0] {
			TypedValue::I64(p) => unsafe {std::mem::transmute::<i64, &RemoteReadRequest<Header>>(p) } ,
			_ => unreachable!(),
		};

		use std::vec::Vec;
		let arg2 = match args[1] {
			TypedValue::I64(p) => unsafe {std::mem::transmute::<i64, &Vec<Vec<u8>>>(p) },
			_ => unreachable!(),
		};

		let res = if check_read_proof_::<Block, Blake2Hasher>(arg1, arg2.clone()).is_err() {
			0
		} else {
			1
		};

		Ok(ReturnValue::Value(TypedValue::I32(res)))
	}


	let mut env_builder = EnvironmentDefinitionBuilder::new();

	let mut state = State {counter: 0};

	env_builder.add_host_func("env", "ext_check_read_proof", check_read_proof);

	let memory = match sandbox::Memory::new(100, Some(100)) {
		Ok(m) => m,
		Err(_) => unreachable!("
				Memory::new() can return Err only if parameters are borked; \
				We passing params here explicitly and they're correct; \
				Memory::new() can't return a Error qed"
		),
	};

	env_builder.add_memory("env", "memory", memory);
	let mut instance = Instance::new(code, &env_builder, &mut state)?;
	// we call check_read_proof there
	let result = instance.invoke(b"check_read_proof", args, &mut state);

	result.map_err(|err| {
		HostError
	})
}

impl OtherApi for () {
	fn run_wasm(request: &RemoteReadRequest<Header>, remote_proof: Vec<Vec<u8>>) {
		let arg1 = request as *const RemoteReadRequest<Header>;
		let arg2 = remote_proof.as_ptr();
		let args = [TypedValue::I64(arg1 as i64), TypedValue::I64(arg2 as i64)];
		let res = execute_wasm(&code, &args);
		println!("result: {:?}", res);
	}
}


// FIXME
#[test]
fn invoke_proof() {
	let code = wabt::wat2wasm(r#"
(module
  (type $t0 (func (result i32)))
  (import "env" "memory" (memory $env.memory 17))
  (import "env" "ext_check_read_proof" (func $ext_check_read_proof (type $t0)))
  (func $check_read_proof (type $t0) (result i32)
    (local $l0 i32)
    call $ext_check_read_proof
    set_local $l0
    get_local $l0
    return)
  (table $__indirect_function_table 1 1 anyfunc)
  (global $__data_end i32 (i32.const 1048610))
  (global $__heap_base i32 (i32.const 1048610))
  (global $__rustc_debug_gdb_scripts_section__ i32 (i32.const 1048576))
  (export "__indirect_function_table" (table 0))
  (export "__data_end" (global 0))
  (export "__heap_base" (global 1))
  (export "__rustc_debug_gdb_scripts_section__" (global 2))
  (export "check_read_proof" (func $check_read_proof))
)		"#).unwrap();

	let result = execute_wasm(
		&code,
		&[],
	);
	assert_eq!(result.unwrap(), ReturnValue::Value(TypedValue::I32(1)));
}
