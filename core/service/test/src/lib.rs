// Copyright 2017-2019 Parity Technologies (UK) Ltd
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Service integration test utils.

use std::iter;
use std::sync::Arc;
use std::net::Ipv4Addr;
use std::time::Duration;
use std::collections::HashMap;
use log::info;
use futures::{Future, Stream};
use tempdir::TempDir;
use tokio::runtime::Runtime;
use tokio::timer::Interval;
use service::{
	ServiceFactory,
	Configuration,
	FactoryFullConfiguration,
	FactoryChainSpec,
	Roles,
	FactoryExtrinsic,
};
use network::{multiaddr, SyncProvider, ManageNetwork};
use network::config::{NetworkConfiguration, NodeKeyConfig, Secret, NonReservedPeerMode};
use sr_primitives::traits::As;
use sr_primitives::generic::BlockId;
use consensus::{ImportBlock, BlockImport};

struct TestNet<F: ServiceFactory> {
	runtime: Runtime,
	authority_nodes: Vec<(u32, Arc<F::FullService>)>,
	full_nodes: Vec<(u32, Arc<F::FullService>)>,
	_light_nodes: Vec<(u32, Arc<F::LightService>)>,
	chain_spec: FactoryChainSpec<F>,
	base_port: u16,
	nodes: usize,
}

impl<F: ServiceFactory> TestNet<F> {
	pub fn run_until_all_full<P: Send + Sync + Fn(u32, &F::FullService) -> bool + 'static>(&mut self, predicate: P) {
		let full_nodes = self.full_nodes.clone();
		let interval = Interval::new_interval(Duration::from_millis(100)).map_err(|_| ()).for_each(move |_| {
			if full_nodes.iter().all(|&(ref id, ref service)| predicate(*id, service)) {
				Err(())
			} else {
				Ok(())
			}
		});
		self.runtime.block_on(interval).ok();
	}
}

fn node_config<F: ServiceFactory> (
	index: u32,
	spec: &FactoryChainSpec<F>,
	role: Roles,
	key_seed: Option<String>,
	base_port: u16,
	root: &TempDir,
) -> FactoryFullConfiguration<F>
{
	let root = root.path().join(format!("node-{}", index));
	let mut keys = Vec::new();
	if let Some(seed) = key_seed {
		keys.push(seed);
	}

	let config_path = Some(String::from(root.join("network").to_str().unwrap()));
	let net_config_path = config_path.clone();

	let network_config = NetworkConfiguration {
		config_path,
		net_config_path,
		listen_addresses: vec! [
			iter::once(multiaddr::Protocol::Ip4(Ipv4Addr::new(127, 0, 0, 1)))
				.chain(iter::once(multiaddr::Protocol::Tcp(base_port + index as u16)))
				.collect()
		],
		public_addresses: vec![],
		boot_nodes: vec![],
		node_key: NodeKeyConfig::Ed25519(Secret::New),
		in_peers: 50,
		out_peers: 450,
		reserved_nodes: vec![],
		non_reserved_mode: NonReservedPeerMode::Accept,
		client_version: "network/test/0.1".to_owned(),
		node_name: "unknown".to_owned(),
		enable_mdns: false,
	};

	Configuration {
		impl_name: "network-test-impl",
		impl_version: "0.1",
		impl_commit: "",
		roles: role,
		transaction_pool: Default::default(),
		network: network_config,
		keystore_path: root.join("key").to_str().unwrap().into(),
		database_path: root.join("db").to_str().unwrap().into(),
		database_cache_size: None,
		pruning: Default::default(),
		keys: keys,
		chain_spec: (*spec).clone(),
		custom: Default::default(),
		name: format!("Node {}", index),
		execution_strategies: Default::default(),
		rpc_http: None,
		rpc_ws: None,
		telemetry_endpoints: None,
		default_heap_pages: None,
		offchain_worker: false,
		force_authoring: false,
		disable_grandpa: false,
	}
}

impl<F: ServiceFactory> TestNet<F> {
	fn new(temp: &TempDir, spec: FactoryChainSpec<F>, full: u32, light: u32, authorities: Vec<String>, base_port: u16) -> TestNet<F> {
		let _ = ::env_logger::try_init();
		::fdlimit::raise_fd_limit();
		let runtime = Runtime::new().expect("Error creating tokio runtime");
		let mut net = TestNet {
			runtime,
			authority_nodes: Default::default(),
			full_nodes: Default::default(),
			_light_nodes: Default::default(),
			chain_spec: spec.clone(),
			base_port,
			nodes: 0,
		};
		net.insert_nodes(temp, full, light, authorities);
		net
	}

	fn insert_nodes(&mut self, temp: &TempDir, full: u32, light: u32, authorities: Vec<String>) {
		let mut nodes = self.nodes;
		let base_port = self.base_port;
		let spec = self.chain_spec.clone();
		let executor = self.runtime.executor();
		self.authority_nodes.extend(authorities.iter().enumerate().map(|(index, key)| ((index + nodes) as u32,
			 Arc::new(F::new_full(node_config::<F>(index as u32, &spec, Roles::AUTHORITY, Some(key.clone()), base_port, &temp), executor.clone())
					  .expect("Error creating test node service")))
		));
		nodes += authorities.len();

		self.full_nodes.extend((nodes..nodes + full as usize).map(|index| (index as u32,
			Arc::new(F::new_full(node_config::<F>(index as u32, &spec, Roles::FULL, None, base_port, &temp), executor.clone())
				.expect("Error creating test node service")))
		));
		nodes += full as usize;

		self._light_nodes.extend((nodes..nodes + light as usize).map(|index| (index as u32,
			Arc::new(F::new_light(node_config::<F>(index as u32, &spec, Roles::LIGHT, None, base_port, &temp), executor.clone())
					 .expect("Error creating test node service")))
		));
		nodes += light as usize;
		self.nodes = nodes;
	}
}

pub fn connectivity<F: ServiceFactory>(spec: FactoryChainSpec<F>) {
	const NUM_NODES: u32 = 10;
	{
		let temp = TempDir::new("substrate-connectivity-test").expect("Error creating test dir");
		let runtime = {
			let mut network = TestNet::<F>::new(&temp, spec.clone(), NUM_NODES, 0, vec![], 30400);
			info!("Checking star topology");
			let first_address = network.full_nodes[0].1.network().node_id().expect("No node address");
			for (_, service) in network.full_nodes.iter().skip(1) {
				service.network().add_reserved_peer(first_address.clone()).expect("Error adding reserved peer");
			}
			network.run_until_all_full(|_index, service|
				service.network().peers().len() == NUM_NODES as usize - 1
			);
			network.runtime
		};

		runtime.shutdown_on_idle().wait().expect("Error shutting down runtime");

		temp.close().expect("Error removing temp dir");
	}
	{
		let temp = TempDir::new("substrate-connectivity-test").expect("Error creating test dir");
		{
			let mut network = TestNet::<F>::new(&temp, spec, NUM_NODES, 0, vec![], 30400);
			info!("Checking linked topology");
			let mut address = network.full_nodes[0].1.network().node_id().expect("No node address");
			for (_, service) in network.full_nodes.iter().skip(1) {
				service.network().add_reserved_peer(address.clone()).expect("Error adding reserved peer");
				address = service.network().node_id().expect("No node address");
			}
			network.run_until_all_full(|_index, service| {
				service.network().peers().len() == NUM_NODES as usize - 1
			});
		}
		temp.close().expect("Error removing temp dir");
	}
}

pub fn sync<F, B, E>(spec: FactoryChainSpec<F>, block_factory: B, extrinsic_factory: E)
where
	F: ServiceFactory,
	B: Fn(&F::FullService) -> ImportBlock<F::Block>,
	E: Fn(&F::FullService) -> FactoryExtrinsic<F>,
{
	const NUM_NODES: u32 = 10;
	const NUM_BLOCKS: usize = 512;
	let temp = TempDir::new("substrate-sync-test").expect("Error creating test dir");
	let mut network = TestNet::<F>::new(&temp, spec.clone(), NUM_NODES, 0, vec![], 30500);
	info!("Checking block sync");
	let first_address = {
		let first_service = &network.full_nodes[0].1;
		for i in 0 .. NUM_BLOCKS {
			if i % 128 == 0 {
				info!("Generating #{}", i);
			}
			let import_data = block_factory(&first_service);
			first_service.client().import_block(import_data, HashMap::new()).expect("Error importing test block");
		}
		first_service.network().node_id().unwrap()
	};
	info!("Running sync");
	for (_, service) in network.full_nodes.iter().skip(1) {
		service.network().add_reserved_peer(first_address.clone()).expect("Error adding reserved peer");
	}
	network.run_until_all_full(|_index, service|
		service.client().info().unwrap().chain.best_number == As::sa(NUM_BLOCKS as u64)
	);
	info!("Checking extrinsic propagation");
	let first_service = network.full_nodes[0].1.clone();
	let best_block = BlockId::number(first_service.client().info().unwrap().chain.best_number);
	first_service.transaction_pool().submit_one(&best_block, extrinsic_factory(&first_service)).unwrap();
	network.run_until_all_full(|_index, service|
		service.transaction_pool().ready().count() == 1
	);
}

pub fn consensus<F>(spec: FactoryChainSpec<F>, authorities: Vec<String>)
	where
		F: ServiceFactory,
{
	const NUM_NODES: u32 = 20;
	const NUM_BLOCKS: u64 = 200;
	let temp = TempDir::new("substrate-conensus-test").expect("Error creating test dir");
	let mut network = TestNet::<F>::new(&temp, spec.clone(), NUM_NODES / 2, 0, authorities, 30600);
	info!("Checking consensus");
	let first_address = network.authority_nodes[0].1.network().node_id().unwrap();
	for (_, service) in network.full_nodes.iter() {
		service.network().add_reserved_peer(first_address.clone()).expect("Error adding reserved peer");
	}
	for (_, service) in network.authority_nodes.iter().skip(1) {
		service.network().add_reserved_peer(first_address.clone()).expect("Error adding reserved peer");
	}
	network.run_until_all_full(|_index, service| {
		service.client().info().unwrap().chain.finalized_number >= As::sa(NUM_BLOCKS / 2)
	});
	info!("Adding more peers");
	network.insert_nodes(&temp, NUM_NODES / 2, 0, vec![]);
	for (_, service) in network.full_nodes.iter() {
		service.network().add_reserved_peer(first_address.clone()).expect("Error adding reserved peer");
	}
	network.run_until_all_full(|_index, service|
		service.client().info().unwrap().chain.finalized_number >= As::sa(NUM_BLOCKS)
	);
}
