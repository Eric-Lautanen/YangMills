with open('src/lean/YangMills/Proofs/ReflectionPositivity.lean', 'r', encoding='utf-8') as f:
    text = f.read()

# Find all comment openers and closers
opens = []
closes = []
for i in range(len(text)-1):
    if text[i] == '/' and text[i+1] == '-':
        opens.append(i)
    if text[i] == '-' and text[i+1] == '/':
        closes.append(i)

print(f"Total /- : {len(opens)}")
print(f"Total -/ : {len(closes)}")

# Match them
depth = 0
unmatched_opens = []
for i in range(len(text)):
    if i in opens:
        depth += 1
        unmatched_opens.append(i)
    if i in closes:
        depth -= 1
        if unmatched_opens:
            unmatched_opens.pop()

if depth > 0:
    print(f"Unmatched at end: depth={depth}")
    # Show the last few unmatched opens
    for pos in unmatched_opens[-5:]:
        line = text[:pos].count('\n') + 1
        print(f"  Position {pos}, line {line}")
else:
    print("All comments properly matched")
