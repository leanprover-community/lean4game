import * as React from 'react'

/** Error boundary as described in https://reactjs.org/docs/error-boundaries.html */
export class ErrorBoundary extends React.Component<{ children?: React.ReactNode }, { error: string | undefined }> {
    constructor(props: {}) {
        super(props)
        this.state = { error: undefined }
    }

    static getDerivedStateFromError(error: any) {
        // Update state so the next render will show the fallback UI.
        return { error: error.toString() }
    }

    componentDidCatch(error: any, errorInfo: any) {
        // You can also log the error to an error reporting service
        return
    }

    render() {
        if (this.state.error) {
            // You can render any custom fallback UI
            return (
                <div>
                    <h1>Error:</h1>
                    {this.state.error}
                    <br />
                    <br />
                    <a className="link pointer dim " onClick={() => this.setState({ error: undefined })}>
                        Click to reload.
                    </a>
                </div>
            )
        }

        return this.props.children
    }
}
