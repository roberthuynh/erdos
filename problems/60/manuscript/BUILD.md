# Building the manuscript

Use a Unicode-aware TeX engine and install the open STIX Two Text and STIX Two Math font families. The source asks fontspec and unicode-math to resolve those family names. It does not require a particular operating system or absolute font directory.

With Tectonic and its TeX resources already cached, run these commands from this manuscript directory:

```sh
mkdir -p build
tectonic --only-cached --untrusted --keep-logs --outdir build main.tex
```

The build writes `build/main.pdf` and `build/main.log`. A successful build should finish with a PDF write and exit status zero. Tectonic can log the absolute font files it discovers locally even though the source contains only portable family names. Other TeX engines can use the same fontspec/unicode-math source if they support the installed STIX Two fonts.
