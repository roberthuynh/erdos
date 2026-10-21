"""Bound a POSIX job and terminate remaining owned descendants on every exit."""
import os
import signal
import subprocess


class JobCancelled(Exception):
    def __init__(self, signum):
        self.signum = signum
        super().__init__('cancelled by signal ' + str(signum))


def run_bounded(command, *, cwd, timeout):
    process = None
    pending_signal = None
    def kill_owned():
        if process is not None:
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
    def cancel(signum, frame):
        nonlocal pending_signal
        if pending_signal is None:
            pending_signal = signum
        # Never raise while Popen may have created a child but has not returned
        # its ownership handle. Defer that cancellation until assignment.
        kill_owned()
    handlers = {sig: signal.signal(sig, cancel) for sig in (signal.SIGTERM, signal.SIGINT)}
    try:
        process = subprocess.Popen(command, cwd=cwd, start_new_session=True)
        if pending_signal is not None:
            raise JobCancelled(pending_signal)
        code = process.wait(timeout=timeout)
        if pending_signal is not None:
            raise JobCancelled(pending_signal)
        return subprocess.CompletedProcess(command, code)
    finally:
        # The new session gives this invocation its own process group. Killing
        # only the leader leaves compiler/download descendants running.
        for sig in handlers:
            signal.signal(sig, signal.SIG_IGN)
        try:
            if process is not None:
                kill_owned()
                process.wait()
        finally:
            for sig, handler in handlers.items():
                signal.signal(sig, handler)
