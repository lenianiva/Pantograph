LIB := ./.lake/build/lib/Pantograph.olean
EXE := ./.lake/build/bin/pantograph
SOURCE := $(wildcard Pantograph/*.lean) $(wildcard *.lean) lean-toolchain

TEST_EXE := ./.lake/build/bin/test
TEST_SOURCE := $(wildcard Test/*.lean)

$(LIB) $(EXE): $(SOURCE)
	lake build pantograph

$(TEST_EXE): $(LIB) $(TEST_SOURCE)
	lake build test

test: $(TEST_EXE)
	$(TEST_EXE)

clean:
	lake clean

.PHONY: test clean
