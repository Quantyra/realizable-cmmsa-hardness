"""Add retained worker nonzero exits and direct archive custody to the transport."""
import ast
import json
from pathlib import Path
import subprocess
from custody_checks import digest

HERE=Path(__file__).resolve().parent


def main():
    source=HERE/'full112_dedicated_openssh_v1.py'
    raw=source.read_bytes()
    assert raw==subprocess.check_output(['git','show','eca22c39:scripts/research/openai-bridge-validation-20261007/'+source.name],cwd=HERE)
    text=raw.decode()
    replacements=[
        ('def call(self, argv, data=None):','def call(self, argv, data=None, allow_failure=False, output_path=None):'),
        ("        with prefix.with_suffix('.stdout').open('xb') as out, prefix.with_suffix('.stderr').open('xb') as err:",
         "        stdout_path = Path(output_path) if output_path is not None else prefix.with_suffix('.stdout')\n        with stdout_path.open('xb') as out, prefix.with_suffix('.stderr').open('xb') as err:"),
        ("            path = prefix.with_suffix('.'+stream)","            path = stdout_path if stream == 'stdout' else prefix.with_suffix('.stderr')"),
        ("        assert process.returncode == 0, 'Original transport failed; preserve and collect without replay'\n        return prefix.with_suffix('.stdout')",
         "        assert process.returncode == 0 or allow_failure, 'Original transport failed; preserve and collect without replay'\n        return stdout_path"),
        ("    def ssh(self, command):\n        return self.call([*self.ssh_argv, command])",
         "    def ssh(self, command, allow_failure=False, output_path=None):\n        return self.call([*self.ssh_argv, command], allow_failure=allow_failure, output_path=output_path)")]
    for old,new in replacements:assert text.count(old)==1;text=text.replace(old,new)
    ast.parse(text)
    target=HERE/'full112_dedicated_openssh_v2.py';target.open('xb').write(text.encode())
    (HERE/'full112-openssh-transport-derivation-v2.json').open('x').write(json.dumps(dict(
        parent=source.name,parent_sha256=digest(source),target=target.name,sha256=digest(target),
        replacements=replacements,native_nonzero_retained=True,no_command_replay=True,
        worker_and_compiler_commands_unchanged=True,compiler_invoked=False,cloud_action=False),indent=2)+'\n')


if __name__=='__main__':main()
