LIB := build/lib/Pantograph.olean
EXE := build/bin/pantograph
SOURCE := $(wildcard Pantograph/*.lean) Main.lean Pantograph.lean

TEST_EXE := build/bin/test
TEST_SOURCE := $(wildcard Test/*.lean)

$(LIB) $(EXE): $(SOURCE)
	lake build

$(TEST_EXE): $(LIB) $(TEST_SOURCE)
	lake build test

test: $(TEST_EXE)
	lake env $(TEST_EXE)

.PHONY: test