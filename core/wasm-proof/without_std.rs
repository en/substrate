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

#[doc(hidden)]
pub use rstd;
pub use rstd::{mem, slice};

use core::{intrinsics, panic::PanicInfo};
use rstd::{vec::Vec, cell::Cell, convert::TryInto};
use primitives::offchain;
use codec::Decode;

/// External (Host) APIs
pub mod ext {
	use super::*;

	/// The state of an exchangeable function.
	#[derive(Clone, Copy)]
	enum ExchangeableFunctionState {
		/// Original function is present
		Original,
		/// The function has been replaced.
		Replaced,
	}

	/// A function which implementation can be exchanged.
	///
	/// Internally this works by swapping function pointers.
	pub struct ExchangeableFunction<T>(Cell<(T, ExchangeableFunctionState)>);

	impl<T> ExchangeableFunction<T> {
		/// Create a new instance of `ExchangeableFunction`.
		pub const fn new(impl_: T) -> Self {
			Self(Cell::new((impl_, ExchangeableFunctionState::Original)))
		}
	}

	impl<T: Copy> ExchangeableFunction<T> {
		/// Replace the implementation with `new_impl`.
		///
		/// # Panics
		///
		/// Panics when trying to replace an already replaced implementation.
		///
		/// # Returns
		///
		/// Returns the original implementation wrapped in [`RestoreImplementation`].
		pub fn replace_implementation(&'static self, new_impl: T) -> RestoreImplementation<T> {
			if let ExchangeableFunctionState::Replaced = self.0.get().1 {
				panic!("Trying to replace an already replaced implementation!")
			}

			let old = self.0.replace((new_impl, ExchangeableFunctionState::Replaced));

			RestoreImplementation(self, Some(old.0))
		}

		/// Restore the original implementation.
		fn restore_orig_implementation(&self, orig: T) {
			self.0.set((orig, ExchangeableFunctionState::Original));
		}

		/// Returns the internal function pointer.
		pub fn get(&self) -> T {
			self.0.get().0
		}
	}

	// WASM does not support threads, so this is safe; qed.
	unsafe impl<T> Sync for ExchangeableFunction<T> {}

	/// Restores a function implementation on drop.
	///
	/// Stores a static reference to the function object and the original implementation.
	pub struct RestoreImplementation<T: 'static + Copy>(&'static ExchangeableFunction<T>, Option<T>);

	impl<T: Copy> Drop for RestoreImplementation<T> {
		fn drop(&mut self) {
			self.0.restore_orig_implementation(self.1.take().expect("Value is only taken on drop; qed"));
		}
	}

	/// Declare extern functions
	macro_rules! extern_functions {
		(
			$(
				$( #[$attr:meta] )*
				fn $name:ident ( $( $arg:ident : $arg_ty:ty ),* $(,)? ) $( -> $ret:ty )?;
			)*
		) => {
			$(
				$( #[$attr] )*
				#[allow(non_upper_case_globals)]
				pub static $name: ExchangeableFunction<unsafe fn ( $( $arg_ty ),* ) $( -> $ret )?> =
					ExchangeableFunction::new(extern_functions_host_impl::$name);
			)*

			/// The exchangeable extern functions host implementations.
			pub(crate) mod extern_functions_host_impl {
				$(
					pub unsafe fn $name ( $( $arg : $arg_ty ),* ) $( -> $ret )? {
						implementation::$name ( $( $arg ),* )
					}
				)*

				mod implementation {
					extern "C" {
						$(
							pub fn $name ( $( $arg : $arg_ty ),* ) $( -> $ret )?;
						)*
					}
				}
			}
		};
	}

	/// Host functions, provided by the executor.
	/// A WebAssembly runtime module would "import" these to access the execution environment
	/// (most importantly, storage) or perform heavy hash calculations.
	/// See also "ext_" functions in sr-sandbox and sr-std
	extern_functions! {
		fn ext_run_wasm();
}

}
pub use self::ext::*;

impl OtherApi for () {
	fn run_wasm(request: &RemoteReadRequest<Header>, remote_proof: Vec<Vec<u8>>) {
		// FIXME: ext_run_wasm not impled
		unsafe {
			ext_run_wasm.get()();
		}
	}
}