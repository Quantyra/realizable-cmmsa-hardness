"""Atomic shared-VM lifecycle decision; cloud shutdown is injected by its owner.

Observation and action occur under the same lock used by thread admission.
No missing, stale, malformed, or incomplete observation authorizes shutdown.
"""
from thread_leases import Busy, locked, phase, write_phase


def drain_and_act(root, *, observe, action):
    with locked(root) as root:
        active = root / 'active'
        if active.exists() and any(active.iterdir()):
            raise Busy('Active or incomplete thread leases')
        if phase(root) != 'ACCEPTING':
            raise Busy('An existing lifecycle action owns this VM')
        # Collect fresh OS/controller observations after taking the admission lock.
        observation = observe()
        if not isinstance(observation, dict):
            raise Busy('No authoritative lifecycle observation')
        required = ('process_scan_complete', 'session_scan_complete',
                    'controller_inventory_complete', 'all_controllers_lease_aware',
                    'idle_threshold_met')
        if any(observation.get(key) is not True for key in required):
            raise Busy('Incomplete or incompatible lifecycle observation')
        workloads = observation.get('unregistered_workloads')
        sessions = observation.get('interactive_sessions')
        if not isinstance(workloads, list) or not isinstance(sessions, list):
            raise Busy('Missing workload/session inventory')
        if workloads or sessions:
            raise Busy('Unregistered work or interactive session is active')
        write_phase(root, 'DRAINING')
        # DRAINING survives exceptions or a failed shutdown. Do not readmit while
        # a delayed shutdown might still execute; recovery belongs to the manager.
        return action(observation)

