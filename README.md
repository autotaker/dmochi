# dmochi 

## How to install
Currently only 64-bits linux systems are supported.

### requirements
- hoice (https://github.com/hopv/hoice)
- stack (https://docs.haskellstack.org/en/stable/README/)

### Build
```bash
make
```

### Test
```bash
make test
```

### Build executable
```bash
make bin # then dmochi-bin/dmochi is the executable
```

## Usage
To verify `target.ml`, 
```bash
dmochi target.ml
```
Verication result will be written at `target.ml.result.json`