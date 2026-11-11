import { Component, type ErrorInfo, type ReactNode } from 'react'

import { ErrorPage } from './ErrorPage'

// see: https://react.dev/reference/react/Component#catching-rendering-errors-with-an-error-boundary

type ErrorBoundaryProps = {
  children: ReactNode
}

type ErrorBoundaryState = {
  error?: Error
}

/** Shows the `ErrorPage` instead of a blank page if rendering `children` throws */
export class ErrorBoundary extends Component<
  ErrorBoundaryProps,
  ErrorBoundaryState
> {
  state: ErrorBoundaryState = {}

  static getDerivedStateFromError(error: Error): ErrorBoundaryState {
    return { error }
  }

  componentDidCatch(error: Error, info: ErrorInfo) {
    console.error('ErrorBoundary caught an error:', error)
    console.error('Component stack:', info.componentStack)
  }

  render() {
    if (this.state.error) {
      return <ErrorPage error={this.state.error} />
    }
    return this.props.children
  }
}
