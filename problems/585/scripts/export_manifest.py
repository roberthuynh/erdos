"""Compatibility import of the collection export boundary for legacy fixtures."""
from pathlib import Path
import importlib.util
_source = Path(__file__).resolve().parents[3] / "scripts/export_manifest.py"
_spec = importlib.util.spec_from_file_location("collection_export_manifest", _source)
_module = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_module)
export_files = _module.export_files
