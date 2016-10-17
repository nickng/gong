FROM ubuntu:16.04
MAINTAINER Nicholas Ng <nickng@imperial.ac.uk>
RUN apt-get -y --no-install-recommends update && \
    apt-get install -y --no-install-recommends haskell-platform git && \
    apt-get clean
RUN cabal update
RUN cd /usr/local/src; git clone git://github.com/nickng/gong.git
RUN cd /usr/local/src/gong; cabal install
RUN cp -v /usr/local/src/gong/dist/build/Gong/Gong /usr/local/bin
CMD /usr/local/bin/Gong
