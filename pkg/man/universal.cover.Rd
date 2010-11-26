\name{universal.cover}
\alias{universal.cover}
\title{ Universal portfolio selection algorithm from Cover }
\description{
  Implement the universal portfolio selection algortihm defined by Cover
  directly, i.e. with exponential complexity in the number of stocks
  considered.
}
\usage{
universal.cover(x, n)
}
\arguments{
  \item{x}{
    Time series of relative prices
}
\item{n}{
  Split any dimension in n, the algorithm will evaluate O(n^(m-1)) CRP, with
  m the number of stocks in x
}
}
\details{
  Straightforward implementation of Cover's algorithm, exponential
  behavior restrict this to small number of stocks.
}
\value{
  Return the time series of portfolio wealths.
}
\references{
  Thomas M. Cover. Universal Portfolios.   Mathematical Finance, 1(1): 1-29, January 1991.
}
\author{ Marc Delvaux
}

