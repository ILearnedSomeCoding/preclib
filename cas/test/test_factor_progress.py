"""Native calculator regression; pass the calculator executable as argv[1]."""
import re
import subprocess
import sys

commands = "\n".join([
    "!progress factorint(2^128+1)",
    "factorint_progress(2^256+1)",
    "factorint_progress(2^512+1)",
    "factorint(202)",
    "!quit",
    "",
])
result = subprocess.run([sys.argv[1]], input=commands, text=True,
                        capture_output=True, timeout=180)
assert result.returncode == 0, result.stderr
assert "{59649589127497217, 5704689200685129054721}" in result.stdout
assert "{1238926361552897, 93461639715357977769163558199606896584051237541638188580280321}" in result.stdout
assert "{2, 101}" in result.stdout
assert "ECM B1=50000 B2=1000000 curves" in result.stderr
assert "SIQS" not in result.stderr
match = re.search(r"known factors: \{([\d, ]+)\}; unresolved cofactor: (\d+)", result.stderr)
assert match, result.stderr
known = [int(x) for x in match[1].split(",")]
assert 2424833 in known
product = int(match[2])
for factor in known:
    product *= factor
assert product == 2**512 + 1
print("factor progress / partial result ok")
print("known factors:", known)
print("unresolved cofactor:", match[2])
