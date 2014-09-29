TARGET = Contract.hs
EXTRACTED = ContractExtracted.hs
HEADER = Header.hs
COQ_FILE = Extraction.v
SED_SCRIPT = '/^data Vars/,$$'p

default: $(TARGET)

Contract.hs: $(EXTRACTED) $(HEADER)
	cp $(HEADER) $(TARGET)
	sed -n $(SED_SCRIPT) $(EXTRACTED) >> $(TARGET)

$(EXTRACTED): $(COQ_FILE)
	coqc $(COQ_FILE)

clean:
	rm -f $(TARGET) $(EXTRACTED)
	rm -r $(COQ_FILE:.v=.vo) $(COQ_FILE:.v=.glob)
