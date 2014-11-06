TARGET = Contract.hs
EXTRACTED = ContractExtracted.hs
HEADER = Header.hs
COQ_FILE = Extraction.v
SED_SCRIPT = '/^type Currency = String/,$$'p

default: $(TARGET)

Contract.hs: $(EXTRACTED) $(HEADER)
	cp $(HEADER) $(TARGET)
	sed -n $(SED_SCRIPT) $(EXTRACTED) >> $(TARGET)

$(EXTRACTED): $(COQ_FILE)
	coqc $(COQ_FILE)

clean:
	rm -rf *~
	rm -f $(TARGET) $(EXTRACTED)
	rm -rf $(COQ_FILE:.v=.vo) $(COQ_FILE:.v=.glob)
