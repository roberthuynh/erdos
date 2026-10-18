import re
"""Comment-aware forbidden proof-token scanner, adapted from published problem 60."""
DISALLOWED = (r"\b(?:sorry|admit|native_decide|ofReduceBool|ofReduceNat|implemented_by|extern|unsafe|axiom)\b"
              r"|decide\s*\+native|debug\.skipKernelTC")


def lean_code(text):
    """Remove comments/plain strings; reject unaudited executable interpolation."""
    result = []
    i = depth = 0
    string = False
    while i < len(text):
        pair = text[i:i + 2]
        if depth:
            if pair == "/-":
                depth += 1
                i += 2
            elif pair == "-/":
                depth -= 1
                i += 2
                result.append(" ")
            else:
                i += 1
        elif string:
            if text[i] == "\\":
                i += 2
            elif text[i] == '"':
                string = False
                i += 1
                result.append(" ")
            else:
                i += 1
        elif pair == "/-":
            depth = 1
            i += 2
        elif pair == "--":
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
        elif text[i] == '"':
            previous = next((c for c in reversed(result) if not c.isspace()), '')
            if previous == '!':
                raise ValueError('Interpolated strings cannot be audited by the source scanner')
            string = True
            i += 1
        else:
            result.append(text[i])
            i += 1
    if depth or string:
        raise ValueError("Unterminated source comment or string")
    return "".join(result)


