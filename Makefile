
# Change this to install into a different directory
LIB_INSTALL_DIR = $${HOME}/.local/lib

ifeq ($(OS),Windows_NT)
  #on windows
  LIB_INSTALL_NAME = 'diffmu-wrapper.*'
else
  #on linux
  LIB_INSTALL_NAME = 'libdiffmu-wrapper.*'
endif


all: capp


usingcabal: ffisrc/Wrapper.hs wrapper.cabal.old
	rm -f wrapper.cabal
	cp wrapper.cabal.old wrapper.cabal
	cabal configure && cabal build
	find dist-newstyle/ -name 'libwrapper.*' -exec cp {} ./capp/ \;


wrapperlib: ffisrc/Wrapper.hs package.yaml stack.yaml
	rm -f DiffPrivacyInferenceHs.cabal
	stack build --ghc-options -j
	find .stack-work/ -name 'libdiffmu-wrapper.*' -exec cp {} ./capp/ \;


capp: wrapperlib
	cd capp && make


run: capp
	cd capp && make run

# --------------------------------------
# simply installing the shared library by copying it


install: wrapperlib-install

wrapperlib-install: ffisrc/Wrapper.hs package.yaml stack.yaml
	rm -f DiffPrivacyInferenceHs.cabal
	stack build --ghc-options -j

	mkdir -p ${LIB_INSTALL_DIR}
	/usr/bin/find .stack-work/ -name ${LIB_INSTALL_NAME} -exec cp {} ${LIB_INSTALL_DIR} \;


# ------------------------------------

clean:
	rm -f wrapper.cabal
	rm -fr dist-newstyle
	stack clean && cd capp && make clean

.PHONY: all usingcabal wrapperlib capp run clean install
