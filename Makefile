
.PHONY: build bin test clean
z3dir=./z3-4.6.0
build: z3-4.6.0
	stack build

$(z3dir): scripts/prepare.sh
	bash scripts/prepare.sh

dist = $(shell stack path --local-install-root)
target = $(dist)/bin/hiboch $(dist)/bin/dmochi $(dist)/bin/tohors

bin: $(target) dmochi.sh $(z3dir)/lib/libz3.so
	mkdir -p dmochi-bin/lib dmochi-bin/bin
	cp $(target) dmochi-bin/bin
	cp $(z3dir)/lib/libz3.so dmochi-bin/lib
	cp dmochi.sh dmochi-bin/dmochi
	chmod a+x dmochi-bin/dmochi

test:
	LD_LIBRARY_PATH=$(z3dir)/lib stack test

clean:
	stack clean
	rm -rf dmochi-bin
