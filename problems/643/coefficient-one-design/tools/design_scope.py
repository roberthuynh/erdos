"""Strict final declaration/resource configuration for the expanded design proof."""
import json
import re


def load_scope(root):
    scope = json.loads((root / 'design-scope.json').read_text())
    expected = {'schema', 'configured', 'target', 'declarations', 'module_lean_flags', 'limitations'}
    if set(scope) != expected or scope['schema'] != 1 or scope['configured'] is not True:
        raise RuntimeError('expanded design scope is not frozen/configured')
    name = re.compile(r'[A-Za-z_][A-Za-z_0-9.]*')
    if not isinstance(scope['target'], str) or not name.fullmatch(scope['target']):
        raise RuntimeError('invalid expanded target')
    declarations = scope['declarations']
    if not isinstance(declarations, dict) or not declarations:
        raise RuntimeError('missing exact expanded declarations')
    for declaration, module in declarations.items():
        if not name.fullmatch(declaration) or not isinstance(module, str) or not name.fullmatch(module):
            raise RuntimeError('invalid expanded declaration ownership')
    for module, flags in scope['module_lean_flags'].items():
        if not name.fullmatch(module) or not isinstance(flags, list) or not flags:
            raise RuntimeError('invalid module resource profile')
        if not all(isinstance(x, str) and re.fullmatch(r'-D(?:maxHeartbeats|maxRecDepth)=\d+', x) for x in flags):
            raise RuntimeError('disallowed resource override')
    if not isinstance(scope['limitations'], list) or not all(isinstance(x, str) for x in scope['limitations']):
        raise RuntimeError('invalid exact limitations')
    return scope
