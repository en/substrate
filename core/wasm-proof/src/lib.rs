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

//! This is part of the Substrate runtime.

#![warn(missing_docs)]

#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(not(feature = "std"), feature(lang_items))]
#![cfg_attr(not(feature = "std"), feature(alloc_error_handler))]
#![cfg_attr(not(feature = "std"), feature(core_intrinsics))]

#![cfg_attr(feature = "std", doc = "Substrate runtime standard library as compiled when linked with Rust's standard library.")]
#![cfg_attr(not(feature = "std"), doc = "Substrate's runtime standard library as compiled without Rust's standard library.")]

use rstd::vec::Vec;

/// Converts a public trait definition into a private trait and set of public functions
/// that assume the trait is implemented for `()` for ease of calling.
macro_rules! export_api {
	(
		$( #[$trait_attr:meta] )*
		pub(crate) trait $trait_name:ident {
			$(
				$( #[$attr:meta] )*
				fn $name:ident
					( $( $arg:ident : $arg_ty:ty ),* $(,)? )
					$( -> $ret:ty )?
					$( where $( $w_name:path : $w_ty:path ),+ )?;
			)*
		}
	) => {
		$( #[$trait_attr] )*
		pub(crate) trait $trait_name {
			$(
				$( #[$attr] )*
				fn $name ( $($arg : $arg_ty ),* ) $( -> $ret )?
				$( where $( $w_name : $w_ty ),+ )?;
			)*
		}

		$(
			$( #[$attr] )*
			pub fn $name ( $($arg : $arg_ty ),* ) $( -> $ret )?
				$( where $( $w_name : $w_ty ),+ )?
			{
				#[allow(deprecated)]
				<()>:: $name ( $( $arg ),* )
			}
		)*
	}
}

export_api! {
	pub(crate) trait OtherApi {
		fn run_wasm();
	}
}

mod imp {
	use super::*;

	#[cfg(feature = "std")]
	include!("../with_std.rs");

	#[cfg(not(feature = "std"))]
	include!("../without_std.rs");
}

#[cfg(not(feature = "std"))]
pub use self::imp::ext::*;